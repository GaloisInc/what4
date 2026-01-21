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
  [ testProperty "propOk" propOk
  , testProperty "propEqNeq" propEqNeq
  , testProperty "propEqSymmetric" propEqSymmetric
  , testProperty "propEqTransitive" propEqTransitive
  , testProperty "propNeqIrreflexive" propNeqIrreflexive
  , testProperty "propNeqSymmetric" propNeqSymmetric
  , testProperty "propEqNeqUnion" propEqNeqUnion
  , testProperty "propUnionEmpty" propUnionEmpty
  , testProperty "propUnionSymmetric" propUnionSymmetric
  ]
  where
  testProperty nm prop =
    TTH.testProperty nm (H.withShrinks 4024 (H.withTests 4096 prop))

-- | Check 'E.ok'
propOk :: H.Property
propOk =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    op <- H.forAll (genEqs (Just sym) genElem)
    case opEqs sym op of
      E.ResTrue -> pure ()
      E.ResFalse -> pure ()
      E.Equalities e -> do
        -- For debugging:
        -- liftIO $ print "~~~~~~~~~~~"
        -- liftIO $ print e
        H.assert (E.ok e)

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
        Monad.when (x /= y) $ do
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
        let eq u v = fst (E.checkEqualPermissive e u v)
        eq x y H.=== eq y x

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
        let (exy, e') = E.checkEqualPermissive e x y
        let (eyz, e'') = E.checkEqualPermissive e' y z
        if exy && eyz
          then True H.=== fst (E.checkEqualPermissive e'' x z)
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
        False H.=== E.checkNotEqualPermissive e x x

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
        Monad.when (x /= y) $
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
        Monad.when (x /= y) $
          case E.union u' v' of
            E.ResTrue -> pure ()
            E.ResFalse -> pure ()
            E.Equalities e -> do
              let debug = do
                    liftIO $ print "~~~~~~~~~~~"
                    liftIO $ putStrLn $ "u  = " ++ show u
                    liftIO $ putStrLn $ "v  = " ++ show v
                    liftIO $ putStrLn $ "u' = " ++ show u'
                    liftIO $ putStrLn $ "v' = " ++ show v'
                    liftIO $ putStrLn $ "e  = " ++ show e
                    liftIO $ putStrLn $ "x  = " ++ show x
                    liftIO $ putStrLn $ "y  = " ++ show y
              let uxy = fst (E.checkEqual u' x y)
              let vxy = fst (E.checkEqual v' x y)
              let exy = fst (E.checkEqual e x y)
              let nuxy = E.checkNotEqual u' x y
              let nvxy = E.checkNotEqual v' x y
              let nexy = E.checkNotEqual e x y
              Monad.when uxy $ do
                Monad.unless exy debug
                H.assert exy
              Monad.when vxy $ do
                Monad.unless exy debug
                H.assert exy
              Monad.when nuxy $ do
                Monad.unless nexy debug
                H.assert nexy
              Monad.when nvxy $ do
                Monad.unless nexy debug
                H.assert nexy
      _ -> pure ()

-- | @x = y@ in @u@ iff @x = y@ in @u /\ empty@.
propUnionEmpty :: H.Property
propUnionEmpty =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    u <- H.forAll (genEqs (Just sym) genElem)
    case opEqs sym u of
      E.ResTrue -> pure ()
      E.ResFalse -> pure ()
      E.Equalities u' ->
        case E.union u' E.empty of
          E.ResTrue -> H.failure
          E.ResFalse -> pure ()
          E.Equalities u'' -> do
            x <- H.forAll genElem
            y <- H.forAll genElem
            Monad.when (x /= y) $
              E.checkEqual u' x y H.=== E.checkEqual u'' x y

-- | @x = y@ in @u /\ v@ iff @x = y@ in @v /\ u@, and same for @!=@.
propUnionSymmetric :: H.Property
propUnionSymmetric =
  H.property $ do
    sym <- liftIO mkSym
    genElem <- liftIO (mkGenElem sym)
    u <- H.forAll (genEqs (Just sym) genElem)
    v <- H.forAll (genEqs (Just sym) genElem)
    case (opEqs sym u, opEqs sym v) of
      (E.Equalities u', E.Equalities v') ->
        case (E.union u' v', E.union v' u') of
          (E.ResTrue, E.ResTrue) -> pure ()
          (E.ResTrue, _) -> H.failure
          (E.ResFalse, E.ResFalse) -> pure ()
          -- it's OK if collapsing or not depends on order
          (E.ResFalse, _) -> pure ()
          (_, E.ResFalse) -> pure ()
          (E.Equalities e, E.Equalities e') -> do
            x <- H.forAll genElem
            y <- H.forAll genElem
            Monad.when (x /= y) $ do
              fst (E.checkEqual e x y) H.=== fst (E.checkEqual e' x y)
              E.checkNotEqual e x y H.=== E.checkNotEqual e' x y
          (E.Equalities _, _) -> H.failure
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
  -- TODO: make inequal
  Empty :: Op sym a (Eqs a)
  Elem :: WI.SymExpr sym a -> Op sym a (Elem a)
  Neq ::
    Op sym a (Eqs a) ->
    Op sym a (Elem a) ->
    Op sym a (Elem a) ->
    Op sym a (Eqs a)
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
      Neq r x y -> fun3 "neq" r x y
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
    Neq r x y ->
      let x' = opEqs sym x in
      let y' = opEqs sym y in
      case opEqs sym r of
        E.ResTrue -> E.fromNotEqualChecked x' y'
        E.ResFalse -> E.ResFalse
        E.Equalities s -> E.notEqualChecked s x' y'
    Union r x y ->
      let x' = opEqs sym x in
      let y' = opEqs sym y in
      case opEqs sym r of
        E.ResTrue -> E.fromEqualChecked x' y'
        E.ResFalse -> E.ResFalse
        E.Equalities s -> E.equalChecked s x' y'
    Query r x y ->
      let x' = opEqs sym x in
      let y' = opEqs sym y in
      case opEqs sym r of
        E.ResTrue -> False
        E.ResFalse -> False
        E.Equalities s -> fst (E.checkEqual s x' y')
