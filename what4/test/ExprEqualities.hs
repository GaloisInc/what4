{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module ExprEqualities (tests) where

import Control.Monad qualified as Monad
import Control.Monad.IO.Class (liftIO)
import Data.Parameterized.Classes (EqF, OrdF, ShowF(showF))
import Data.Parameterized.Nonce (GlobalNonceGenerator, globalNonceGenerator)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Test.Tasty qualified as TT
import Test.Tasty.Hedgehog qualified as TTH
import What4.Expr (EmptyExprBuilderState(EmptyExprBuilderState), Flags)
import What4.Expr.Builder (ExprBuilder, newExprBuilder)
import What4.ExprEqualities qualified as E
import What4.FloatMode (FloatIEEE, FloatModeRepr(FloatIEEERepr))
import What4.Interface qualified as WI

tests :: TT.TestTree
tests =
  TT.testGroup "ExprEqualities"
  [ TTH.testProperty "propEqNeq" propEqNeq
  , TTH.testProperty "propEqSymmetric" propEqSymmetric
  , TTH.testProperty "propEqTransitive" propEqTransitive
  , TTH.testProperty "propNeqIrreflexive" propNeqIrreflexive
  , TTH.testProperty "propNeqSymmetric" propNeqSymmetric
  , TTH.testProperty "propEqNeqUnion" propEqNeqUnion
  ]

-- | @x = y@ implies @not (x != y)@, and vice-versa 
propEqNeq :: H.Property
propEqNeq =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    op <- H.forAll (genEqs (Just sym) genElem)
    case opEqs sym op of
      E.ResTrue -> pure ()
      E.ResFalse -> pure ()
      E.Equalities e -> do
        x <- H.forAll genElem
        y <- H.forAll genElem
        let eqNeq =
              if fst (E.checkEqual e x y)
              then not (E.checkNotEqual e x y)
              else True
        let neqEq =
              if E.checkNotEqual e x y
              then not (fst (E.checkEqual e x y))
              else True
        H.assert (eqNeq && neqEq)

-- | @x = y@ if and only if @y = x@
propEqSymmetric :: H.Property
propEqSymmetric =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    op <- H.forAll (genEqs (Just sym) genElem)
    case opEqs sym op of
      E.ResTrue -> pure ()
      E.ResFalse -> pure ()
      E.Equalities e -> do
        x <- H.forAll genElem
        y <- H.forAll genElem
        fst (E.checkEqual e x y) H.=== fst (E.checkEqual e y x)

-- | @x = y@ and @y = z@ imply @x = z@
propEqTransitive :: H.Property
propEqTransitive =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    op <- H.forAll (genEqs (Just sym) genElem)
    case opEqs sym op of
      E.ResTrue -> pure ()
      E.ResFalse -> pure ()
      E.Equalities e -> do
        x <- H.forAll genElem
        y <- H.forAll genElem
        z <- H.forAll genElem
        let (exy, e') = E.checkEqual e x y
        let (eyz, e'') = E.checkEqual e' y z
        if exy && eyz
          then True H.=== fst (E.checkEqual e'' x z)
          else pure ()

-- | It is not the case that @x /= x@
propNeqIrreflexive :: H.Property
propNeqIrreflexive =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    op <- H.forAll (genEqs (Just sym) genElem)
    case opEqs sym op of
      E.ResTrue -> pure ()
      E.ResFalse -> pure ()
      E.Equalities e -> do
        x <- H.forAll genElem
        False H.=== E.checkNotEqual e x x

-- | @x /= y@ if and only if @y /= x@
propNeqSymmetric :: H.Property
propNeqSymmetric =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    op <- H.forAll (genEqs (Just sym) genElem)
    case opEqs sym op of
      E.ResTrue -> pure ()
      E.ResFalse -> pure ()
      E.Equalities e -> do
        x <- H.forAll genElem
        y <- H.forAll genElem
        E.checkNotEqual e x y H.=== E.checkNotEqual e y x

-- | if @x = y@ in @u@ then @x = y@ in @u /\ v@, and same with @!=@.
propEqNeqUnion :: H.Property
propEqNeqUnion =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    u <- H.forAll (genEqs (Just sym) genElem)
    v <- H.forAll (genEqs (Just sym) genElem)
    case (opEqs sym u, opEqs sym v) of
      (E.Equalities u', E.Equalities v') -> do
        x <- H.forAll genElem
        y <- H.forAll genElem
        Monad.when (fst (E.checkEqual u' x y)) $
          case E.union u' v' of
            E.Equalities e -> H.assert (fst (E.checkEqual e x y))
            _ -> pure ()
        Monad.when (E.checkNotEqual u' x y) $
          case E.union u' v' of
            E.Equalities e -> H.assert (E.checkNotEqual e x y)
            _ -> pure ()
      _ -> pure ()

---------------------------------------------------------------------
-- Helpers

mkSym :: IO (ExprBuilder GlobalNonceGenerator EmptyExprBuilderState (Flags FloatIEEE))
mkSym = newExprBuilder FloatIEEERepr EmptyExprBuilderState globalNonceGenerator

mkGenElem ::
  WI.IsSymExprBuilder sym =>
  sym ->
  IO (H.Gen (WI.SymExpr sym WI.BaseBoolType))
mkGenElem sym = do
  let consts = [WI.truePred sym, WI.falsePred sym]
  vars <-
    Monad.forM [(0 :: Int)..20] $ \i -> do
      let nm = WI.safeSymbol ("b" ++ show i)
      WI.freshConstant sym nm WI.BaseBoolRepr
  pure $ Gen.choice (map pure (consts ++ vars))

---------------------------------------------------------------------
-- Op

data Elem a deriving Show
data Eqs a deriving Show

type family AsEqualities sym t where
  AsEqualities sym (Eqs a) = E.Result (WI.SymExpr sym)
  AsEqualities sym (Elem a) = WI.SymExpr sym a
  AsEqualities sym a = a

-- | An interaction with the 'ExprEqualities' API
data Op sym a t where
  Empty :: Op sym a (Eqs a)
  Elem :: WI.SymExpr sym a -> Op sym a (Elem a)
  Union ::
    Op sym a (Eqs a) ->
    Op sym a (Elem a) ->
    Op sym a (Elem a) ->
    Op sym a (Eqs a)
  Query ::
    Op sym a (Eqs a) ->
    Op sym a (Elem a) ->
    Op sym a (Elem a) ->
    Op sym a Bool

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

instance ShowF (WI.SymExpr sym) => Show (Op sym a t) where
  show =
    \case
      Empty -> "empty"
      Elem a -> showF a
      Union r x y -> fun3 "union" r x y
      Query r x y -> fun3 "query" r x y

---------------------------------------------------------------------
-- Generating Op

-- TODO: Take an Assignment of generators for different types

_genBool ::
  proxy sym ->
  H.Gen (WI.SymExpr sym a) ->
  H.Gen (Op sym a Bool)
_genBool proxy genA =
  Query
  <$> genEqs proxy genA
  <*> (Elem <$> genA)
  <*> (Elem <$> genA)

genEqs ::
  proxy sym ->
  H.Gen (WI.SymExpr sym a) ->
  H.Gen (Op sym a (Eqs a))
genEqs proxy genA =
  Gen.recursive
    Gen.choice
    [ pure Empty
    ]
    [ Union
      <$> genEqs proxy genA
      <*> (Elem <$> genA)
      <*> (Elem <$> genA)
    ]

---------------------------------------------------------------------
-- Interpreting Op

opEqs ::
  EqF (WI.SymExpr sym) =>
  OrdF (WI.SymExpr sym) =>
  WI.IsExpr (WI.SymExpr sym) =>
  sym ->
  Op sym a t ->
  AsEqualities sym t
opEqs sym =
  \case
    Empty -> E.Equalities E.empty
    Elem a -> a
    Union r x y ->
      let x' = opEqs sym x in
      let y' = opEqs sym y in
      case opEqs sym r of
        E.ResTrue -> E.fromEqual x' y'
        E.ResFalse -> E.ResFalse
        E.Equalities s -> E.equal s x' y'
    Query r x y ->
      let x' = opEqs sym x in
      let y' = opEqs sym y in
      case opEqs sym r of
        E.ResTrue -> False
        E.ResFalse -> False
        E.Equalities s -> fst (E.checkEqual s x' y')
