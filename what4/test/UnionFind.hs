{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}

module UnionFind (tests) where

import Data.Maybe qualified as Maybe
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
  [ TTH.testProperty "propSameBool" propSameBool
  , TTH.testProperty "propSameRel" propSameRel

  -- Properties
  , TTH.testProperty "propReflexive" propReflexive
  , TTH.testProperty "propSymmetric" propSymmetric
  , TTH.testProperty "propTransitive" propTransitive

  -- Concrete test cases that have failed in the past
  , TTHU.testCase "(query empty 0 0)" $
      diffTest (Query Empty (Elem 0) (Elem 0))
  , TTHU.testCase "(query (union (union empty 0 1) 0 1) 0 1)" $ do
      let e0 = Elem 0
      let e1 = Elem 1
      diffTest (Query (Union (Union Empty e0 e1) e0 e1) e0 e1)
  ]
  where
    diffTest :: Op Int Bool -> TTHU.Assertion
    diffTest op = do
      let s = opSet op
      let u = opUf op
      s TTHU.@=? u

-- Differential testing vs. a simpler model
propSameBool :: H.Property
propSameBool =
  H.property $ do
    op <- H.forAll (genBool (Gen.int (Range.linear 0 32)))
    let s = opSet op
    let u = opUf op
    s H.=== u

-- Differential testing vs. a simpler model
propSameRel :: H.Property
propSameRel =
  H.property $ do
    op <- H.forAll (genEqRel (Gen.int (Range.linear 0 32)))
    let s = opSet op
    UF.SomeUnionFind u <- pure (opUf op)
    -- This isn't as fine-grained as it could theoretically be, because
    -- `fromBasis` performs reflexive-symmetric-transitive closure. However,
    -- it's still actually caught bugs and prints out a nice representation of
    -- the differences between the relations.
    s H.=== fromBasis (snd (UF.basis u))

propReflexive :: H.Property
propReflexive =
  H.property $ do
    let genElem = Gen.int (Range.linear 0 32)
    op <- H.forAll (genEqRel genElem)
    UF.SomeUnionFind u <- pure (opUf op)
    x <- H.forAll genElem
    let u' = UF.findUnionFind (UF.insert u x ())
    True H.=== Maybe.isJust (UF.equal u' x x)

propSymmetric :: H.Property
propSymmetric =
  H.property $ do
    let genElem = Gen.int (Range.linear 0 32)
    op <- H.forAll (genEqRel genElem)
    UF.SomeUnionFind u <- pure (opUf op)
    x <- H.forAll genElem
    y <- H.forAll genElem
    Maybe.isJust (UF.equal u x y) H.=== Maybe.isJust (UF.equal u y x)

propTransitive :: H.Property
propTransitive =
  H.property $ do
    let genElem = Gen.int (Range.linear 0 32)
    op <- H.forAll (genEqRel genElem)
    UF.SomeUnionFind u <- pure (opUf op)
    x <- H.forAll genElem
    y <- H.forAll genElem
    z <- H.forAll genElem
    case UF.equal u x y of
      Nothing -> pure ()
      Just fxy ->
        case UF.equal (UF.findUnionFind fxy) y z of
          Nothing -> pure ()
          Just fyz ->
            True H.=== Maybe.isJust (UF.equal (UF.findUnionFind fyz) x z)

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
genEqRel genA =
  Gen.recursive
    Gen.choice
    [ pure Empty
    ]
    [ Insert
      <$> genEqRel genA
      <*> (Elem <$> genA)
    , Union
      <$> genEqRel genA
      <*> (Elem <$> genA)
      <*> (Elem <$> genA)
    ]

---------------------------------------------------------------------
-- SetEqRel

-- | Simple, unoptimized model of an equivalence relation
newtype SetEqRel a = SetEqRel (Set (a, a))
  deriving (Eq, Show)

empty :: SetEqRel a
empty = SetEqRel Set.empty

fromBasis :: Ord a => [(UF.Annotated ann a, a)] -> SetEqRel a
fromBasis = foldr (\(UF.Annotated _ root, v) s -> union s root v) empty

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
union (SetEqRel eq) l r =
  SetEqRel (go (Set.insert (l, r) eq))
  where
    go s =
      let s' = closure s in
      if s == s'
      then s'
      else go s'

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
    Union r x y ->
      let x' = opSet x in
      let y' = opSet y in
      union (insert (insert (opSet r) x') y') x' y'
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
        UF.SomeUnionFind u' -> Maybe.isJust (UF.equal u' (opUf x) (opUf y))
