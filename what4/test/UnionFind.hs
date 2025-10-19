{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}

module UnionFind (tests) where

import Data.Set (Set)
import Data.Set qualified as Set
import Test.Tasty qualified as TT
import What4.UnionFind (SomeUnionFind)
import What4.UnionFind qualified as UF
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty.Hedgehog qualified as TTH
import Test.Tasty.HUnit qualified as TTHU

tests :: TT.TestTree
tests =
  TT.testGroup "UnionFind"
  [ TTH.testProperty "propSame" propSame

  -- Concrete test cases that have failed in the past
  , TTHU.testCase "concrete test 1" $ do
      testCase (Query Empty (Elem 0) (Elem 0))
  ]
  where
    testCase :: Op Int Bool -> TTHU.Assertion
    testCase op = do
      let s = opSet op
      let u = opUf op
      s TTHU.@=? u

propSame :: H.Property
propSame =
  H.property $ do
    op <- H.forAll (genBool (Gen.int (Range.linear 0 32)))
    let s = opSet op
    let u = opUf op
    s H.=== u

---------------------------------------------------------------------
-- Op

data Elem a deriving Show
data EqRel a deriving Show

type family AsSet t where
  AsSet (EqRel a) = SetEqRel a
  AsSet (Elem a) = a
  AsSet a = a

type family AsUnionFind t where
  AsUnionFind (EqRel a) = SomeUnionFind () a
  AsUnionFind (Elem a) = a
  AsUnionFind a = a

-- | An interaction with the 'SymSequence' API
data Op a t where
  Empty :: Op a (EqRel a)
  Elem :: a -> Op a (Elem a)
  Insert :: Op a (EqRel a) -> Op a (Elem a) -> Op a (EqRel a)
  Union ::
    Op a (EqRel a) ->
    Op a (Elem a) ->
    Op a (Elem a) ->
    Op a (EqRel a)
  Query ::
    Op a (EqRel a) ->
    Op a (Elem a) ->
    Op a (Elem a) ->
    Op a Bool

sexp :: [String] -> String
sexp s = '(' : (unwords s ++ ")")

fun :: String -> [String] -> String
fun f s = sexp (f:s)

_fun1 :: Show a => String -> a -> String
_fun1 f a = fun f [show a]

fun2 :: (Show a, Show b) => String -> a -> b -> String
fun2 f a b = fun f [show a, show b]

fun3 :: (Show a, Show b, Show c) => String -> a -> b -> c -> String
fun3 f a b c = fun f [show a, show b, show c]

instance Show a => Show (Op a t) where
  show =
    \case
      Empty -> "empty"
      Elem a -> show a
      Insert r e -> fun2 "insert" r e
      Union r x y -> fun3 "union" r x y
      Query r x y -> fun3 "query" r x y

---------------------------------------------------------------------
-- Generating Op

genBool :: H.Gen a -> H.Gen (Op a Bool)
genBool genA =
  Query
  <$> genEqRel genA
  <*> (Elem <$> genA)
  <*> (Elem <$> genA)

genEqRel :: H.Gen a -> H.Gen (Op a (EqRel a))
genEqRel _genA =
  Gen.recursive
    Gen.choice
    [ pure Empty
    ]
    [ -- TODO
    ]

---------------------------------------------------------------------
-- SetEqRel

-- | Simple, unoptimized model of an equivalence relation
newtype SetEqRel a = SetEqRel (Set (a, a))

empty :: SetEqRel a
empty = SetEqRel Set.empty

insert ::
  Ord a =>
  SetEqRel a ->
  a ->
  SetEqRel a
insert (SetEqRel r) e = SetEqRel (Set.insert (e, e) r)

union ::
  Ord a =>
  SetEqRel a ->
  a ->
  a ->
  SetEqRel a
union (SetEqRel eq) l r = SetEqRel (closure (Set.insert (l, r) eq))
  where
    closure :: Ord a => Set (a, a) -> Set (a, a)
    closure e =
      let le = Set.toList e in
      Set.unions
      [ e
      , Set.fromList  -- symmetric closure
        [ (y, x)
        | (x, y) <- le
        ]
      , Set.fromList  -- transitive closure
        [ (x, z)
        | (x, u) <- le
        , (v, z) <- le
        , u == v
        ]
      ]

query ::
  Ord a =>
  SetEqRel a ->
  a ->
  a ->
  Bool
query (SetEqRel r) x y = Set.member (x, y) r

---------------------------------------------------------------------
-- Interpreting Op

opSet :: Ord a => Op a t -> AsSet t
opSet =
  \case
    Empty -> empty
    Elem a -> a
    Insert rel e -> insert (opSet rel) (opSet e)
    Union r x y -> union (opSet r) (opSet x) (opSet y)
    Query r x y -> query (opSet r) (opSet x) (opSet y)

opUf :: Ord a => Op a t -> AsUnionFind t
opUf =
  \case
    Empty -> UF.empty
    Elem a -> a
    Insert u e ->
      case opUf u of
        UF.SomeUnionFind u' ->
          UF.SomeUnionFind (UF.findUnionFind (UF.insert u' (opUf e) ()))
    Union u x y ->
      case opUf u of
        UF.SomeUnionFind u' ->
          let x' = UF.Annotated () (opUf x) in
          let y' = UF.Annotated () (opUf y) in
          UF.SomeUnionFind (fst (UF.unionByValue u' x' y'))
    Query u x y ->
      case opUf u of
        UF.SomeUnionFind u' ->
          case (UF.findByValue u' (opUf x), UF.findByValue u' (opUf y)) of
            (Nothing, Nothing) -> True
            (Just _, Nothing) -> False
            (Nothing, Just _) -> False
            (Just fx, Just fy) -> UF.findKey fx == UF.findKey fy
