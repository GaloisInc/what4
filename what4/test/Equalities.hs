{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Equalities (tests) where

import Control.Monad qualified as Monad
import Control.Monad.IO.Class (liftIO)
import Data.Kind (Type)
import Data.Maybe qualified as Maybe
import Data.Parameterized.Classes (EqF, OrdF)
import Data.Parameterized.Nonce qualified as N
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Test.Tasty qualified as TT
import Test.Tasty.Hedgehog qualified as TTH
import What4.Equalities qualified as E

tests :: TT.TestTree
tests =
  TT.testGroup "Equalities"
  [ TTH.testProperty "propEqNeq" propEqNeq
  ]

mkGenElem :: IO (H.Gen (N.Nonce N.GlobalNonceGenerator ()))
mkGenElem = do
  nonces <-
    Monad.forM ([(0 :: Int)..20]) $ \_ -> do
      n <- N.freshNonce N.globalNonceGenerator
      pure n
  pure (Gen.choice (map pure nonces))

-- | @x = y@ implies @not (x != y)@, and vice-versa 
propEqNeq :: H.Property
propEqNeq =
  H.property $ do
    genElem <- liftIO mkGenElem
    op <- H.forAll (genEqs genElem)
    case opEqs op of
      Nothing -> pure ()
      Just e -> do
        x <- H.forAll genElem
        y <- H.forAll genElem
        Monad.when (x /= y) $ do
          let eqNeq =
                if Maybe.isJust (E.checkEqual e x y)
                then not (E.checkNotEqual e x y)
                else True
          let neqEq =
                if E.checkNotEqual e x y
                then not (Maybe.isJust (E.checkEqual e x y))
                else True
          H.assert (eqNeq && neqEq)

---------------------------------------------------------------------
-- Op

data Elem
data Eqs

type AsEqualities :: (Type -> Type) -> Type -> Type -> Type
type family AsEqualities f a t where
  AsEqualities f _ Eqs = Maybe (E.Equalities f)
  AsEqualities f a Elem = f a
  AsEqualities _ _ x = x

-- | An interaction with the 'E.Equalities' API
type Op :: (Type -> Type) -> Type -> Type -> Type
data Op f a t where
  Empty :: Op f a Eqs
  Elem :: f a -> Op f a Elem
  Neq ::
    Op f a Eqs ->
    Op f a Elem ->
    Op f a Elem ->
    Op f a Eqs
  Union ::
    Op f a Eqs ->
    Op f a Elem ->
    Op f a Elem ->
    Op f a Eqs
  Query ::
    Op f a Eqs ->
    Op f a Elem ->
    Op f a Elem ->
    Op f a Bool

sexp :: [String] -> String
sexp s = '(' : (unwords s ++ ")")

fun :: String -> [String] -> String
fun f s = sexp (f:s)

_fun1 :: Show a => String -> a -> String
_fun1 f a = fun f [show a]

_fun2 :: (Show a, Show b) => String -> a -> b -> String
_fun2 f a b = fun f [show a, show b]

fun3 :: (Show a, Show b, Show c) => String -> a -> b -> c -> String
fun3 f a b c = fun f [show a, show b, show c]

instance Show (f a) => Show (Op f a t) where
  show =
    \case
      Empty -> "empty"
      Elem a -> show a
      Neq r x y -> fun3 "neq" r x y
      Union r x y -> fun3 "union" r x y
      Query r x y -> fun3 "query" r x y

---------------------------------------------------------------------
-- Generating Op

genEqs :: H.Gen (f a) -> H.Gen (Op f a Eqs)
genEqs genA =
  Gen.recursive
    Gen.choice
    [ pure Empty
    ]
    [ Neq
      <$> genEqs genA
      <*> (Elem <$> genA)
      <*> (Elem <$> genA)
    , Union
      <$> genEqs genA
      <*> (Elem <$> genA)
      <*> (Elem <$> genA)
    ]

---------------------------------------------------------------------
-- Interpreting Op

opEqs ::
  EqF f =>
  OrdF f =>
  Op f a t ->
  AsEqualities f a t
opEqs =
  \case
    Empty -> Just E.empty
    Elem a -> a
    Neq r x y -> do
      let x' = opEqs x
      let y' = opEqs y
      r' <- opEqs r
      E.notEqual r' x' y'
    Union r x y -> do
      let x' = opEqs x
      let y' = opEqs y
      r' <- opEqs r
      f <- E.equal r' x' y'
      Just (E.findEqualities  f)
    Query r x y -> do
      let x' = opEqs x
      let y' = opEqs y
      let r' = opEqs r
      case r' of
        Nothing -> False
        Just r'' -> Maybe.isJust (E.checkEqual r'' x' y')
