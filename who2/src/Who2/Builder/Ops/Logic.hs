{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Builder.Ops.Logic
  ( eq
  , andPred
  , notPred
  , orPred
  , xorPred
  , ite
  , itePred
  , bvUlt
  , bvUle
  , bvSlt
  , bvSle
  , bvIsNonzero
  ) where

import           Data.Parameterized.NatRepr (type (<=), NatRepr)
import qualified Data.Parameterized.Classes as PC

import qualified Data.BitVector.Sized as BV
import           Data.Coerce (coerce)

import qualified What4.BaseTypes as BT
import qualified What4.Utils.AbstractDomains as AD
import qualified What4.Utils.BVDomain as BVD

import Data.Hashable (Hashable)

import Who2.Expr (Expr, HasBaseType(baseType))
import qualified Who2.Expr as E
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.Views as EV
import qualified Who2.Expr.Bloom.Polarized as PBS
import qualified Who2.Config as Config

isTrue :: Expr t f BT.BaseBoolType -> Bool
isTrue e = AD.getAbsValue e == Just True
{-# INLINE isTrue #-}

isFalse :: Expr t f BT.BaseBoolType -> Bool
isFalse e = AD.getAbsValue e == Just False
{-# INLINE isFalse #-}

eq ::
  ( HasBaseType (f (Expr t f))
  , AD.Abstractable tp
  , Eq (Expr t f tp)
  , EV.HasLogicViews f
  ) =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f tp ->
  Expr t f tp ->
  IO (Expr t f BT.BaseBoolType)
eq trueExpr falseExpr alloc x y
    -- x == x = true
    -- test: eq-reflexive-bool
    -- test: eq-reflexive-bv
    -- test: bvnonzero-zero
  | x == y = pure trueExpr
  | Just b <- AD.avCheckEq (E.baseType x) (E.eAbsVal x) (E.eAbsVal y) =
      pure $ if b then trueExpr else falseExpr
  | otherwise = case E.baseType x of
      BT.BaseBoolRepr -> eqBool trueExpr falseExpr alloc x y
      _ -> alloc (EL.EqPred x y) Nothing
{-# INLINE eq #-}

-- | Equality on boolean expressions with additional simplifications
eqBool ::
  ( HasBaseType (f (Expr t f))
  , EV.HasLogicViews f
  , Eq (Expr t f BT.BaseBoolType)
  ) =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  IO (Expr t f BT.BaseBoolType)
eqBool trueExpr falseExpr alloc x y
    -- (not a) == b = xor a b
    -- test: eq-not-left
  | Just a <- EV.asNotPred x = xorPred trueExpr falseExpr alloc a y
    -- a == (not b) = xor a b
  | Just b <- EV.asNotPred y = xorPred trueExpr falseExpr alloc x b
    -- true == y = y
    -- test: eq-true
  | isTrue x = pure y
    -- x == true = x
  | isTrue y = pure x
    -- false == y = not y
    -- test: eq-false
  | isFalse x = notPred trueExpr falseExpr alloc y
    -- x == false = not x
  | isFalse y = notPred trueExpr falseExpr alloc x
  | otherwise = alloc (EL.EqPred x y) Nothing
{-# INLINE eqBool #-}

andPred ::
  ( HasBaseType (f (Expr t f))
  , EV.HasLogicViews f
  , Eq (Expr t f BT.BaseBoolType)
  , Hashable (Expr t f BT.BaseBoolType)
  , PC.HashableF (f (Expr t f))
  ) =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp. EL.LogicExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  IO (Expr t f BT.BaseBoolType)
andPred trueExpr falseExpr alloc x y
    -- true && y = y
    -- test: and-true-left
  | isTrue x = pure y
    -- x && true = x
    -- test: and-true-right
  | isTrue y = pure x
    -- false && y = false
    -- test: and-false-left
  | isFalse x = pure falseExpr
    -- x && false = false
    -- test: and-false-right
  | isFalse y = pure falseExpr
    -- x && x = x
    -- test: and-idempotent
  | x == y = pure x
    -- x && (not x) = false
    -- test: and-contradiction
  | Just nx <- EV.asNotPred y, x == nx = pure falseExpr
  | Just nx <- EV.asNotPred x, nx == y = pure falseExpr
    -- (not a) && (not b) = not (a || b)
    -- test: and-demorgan
  | not Config.normalizeOr
  , Just a <- EV.asNotPred x
  , Just b <- EV.asNotPred y = do
      orResult <- orPred trueExpr falseExpr alloc a b
      notPred trueExpr falseExpr alloc orResult
    -- (x1 && ... && xn) && (y1 && ... && yn) = x1 && ... && xn && y1 && ... && yn
    -- test: and-nested-contradiction
    -- test: and-three-way-contradiction
    -- test: and-nested-flatten
  | Just xPol <- EV.asAndPred x
  , Just yPol <- EV.asAndPred y = fromMerged (PBS.merge (coerce xPol) (coerce yPol))
    -- (x1 && ... && xn) && y = x1 && ... && xn && y
    -- x && (y1 && ... && yn) = y1 && ... && yn && x
    -- test: and-insert-contradiction
  | Just xPol <- EV.asAndPred x = insertIntoAndPred (coerce xPol) y x
  | Just yPol <- EV.asAndPred y = insertIntoAndPred (coerce yPol) x y
    -- x && y = x && y
  | otherwise =
      let x' = E.minByHash x y
          y' = E.maxByHash x y
      in fromSimplified (PBS.fromTwo (EL.BoolExprWrapper x') (EL.BoolExprWrapper y'))
  where
    collapsed = pure falseExpr
    fromMerged =
      \case
        Just pbs -> alloc (EL.AndPred pbs) Nothing
        -- (x1 && ... && xn) && (y1 && ... && ~xi && ... && yn) = false
        Nothing -> collapsed
    fromSimplified =
      \case
        PBS.Inconsistent -> collapsed
        PBS.SinglePositive (EL.BoolExprWrapper e) -> pure e
        PBS.SingleNegative (EL.BoolExprWrapper e) -> notPred trueExpr falseExpr alloc e
        PBS.Merged pbs -> alloc (EL.AndPred pbs) Nothing
    -- Insert a single element into an existing AndPred
    insertIntoAndPred pol newElem unchanged =
      case PBS.insertIfNotPresent pol (EL.BoolExprWrapper newElem) of
        Nothing -> collapsed
        Just newPol ->
          if PBS.totalSize newPol == PBS.totalSize pol
          then pure unchanged
          else alloc (EL.AndPred newPol) Nothing
{-# INLINE andPred #-}

notPred ::
  (HasBaseType (f (Expr t f)), EV.HasLogicViews f) =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp. EL.LogicExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f BT.BaseBoolType ->
  IO (Expr t f BT.BaseBoolType)
notPred trueExpr falseExpr alloc x
    -- not true = false
    -- test: not-true
  | isTrue x = pure falseExpr
    -- not false = true
    -- test: not-false
  | isFalse x = pure trueExpr
    -- not (not x) = x
    -- test: not-not
  | Just inner <- EV.asNotPred x = pure inner
  | otherwise = alloc (EL.NotPred x) Nothing
{-# INLINE notPred #-}

orPred ::
  ( HasBaseType (f (Expr t f))
  , EV.HasLogicViews f
  , Eq (Expr t f BT.BaseBoolType)
  , Hashable (Expr t f BT.BaseBoolType)
  , PC.HashableF (f (Expr t f))
  ) =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp. EL.LogicExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  IO (Expr t f BT.BaseBoolType)
orPred trueExpr falseExpr alloc x y
    -- x || y = not (not x && not y)
  | Config.normalizeOr = do
      nx <- notPred trueExpr falseExpr alloc x
      ny <- notPred trueExpr falseExpr alloc y
      andResult <- andPred trueExpr falseExpr alloc nx ny
      notPred trueExpr falseExpr alloc andResult
    -- true || y = true
    -- test: or-true-left
  | isTrue x = pure trueExpr
    -- x || true = true
    -- test: or-true-right
  | isTrue y = pure trueExpr
    -- false || y = y
    -- test: or-false-left
  | isFalse x = pure y
    -- x || false = x
    -- test: or-false-right
  | isFalse y = pure x
    -- x || x = x
    -- test: or-idempotent
  | x == y = pure x
    -- x || (not x) = true
    -- test: or-tautology
  | Just nx <- EV.asNotPred y, x == nx = pure trueExpr
  | Just nx <- EV.asNotPred x, nx == y = pure trueExpr
    -- (not a) || (not b) = not (a && b)
    -- test: or-demorgan
  | Just a <- EV.asNotPred x
  , Just b <- EV.asNotPred y = do
      andResult <- andPred trueExpr falseExpr alloc a b
      notPred trueExpr falseExpr alloc andResult
    -- (x1 || ... || xn) || (y1 || ... || yn) = x1 || ... || xn || y1 || ... || yn
    -- test: or-nested-tautology
    -- test: or-three-way-tautology
    -- test: or-nested-flatten
  | Just xPol <- EV.asOrPred x
  , Just yPol <- EV.asOrPred y = fromMerged (PBS.merge (coerce xPol) (coerce yPol))
    -- (x1 || ... || xn) || y = x1 || ... || xn || y
    -- x || (y1 || ... || yn) = y1 || ... || yn || x
    -- test: or-insert-tautology
  | Just xPol <- EV.asOrPred x = insertIntoOrPred (coerce xPol) y x
  | Just yPol <- EV.asOrPred y = insertIntoOrPred (coerce yPol) x y
    -- x || y = x || y
  | otherwise =
      let x' = E.minByHash x y
          y' = E.maxByHash x y
      in fromSimplified (PBS.fromTwo (EL.BoolExprWrapper x') (EL.BoolExprWrapper y'))
  where
    collapsed = pure trueExpr
    fromMerged =
      \case
        Just pbs -> alloc (EL.OrPred pbs) Nothing
        -- (x1 || ... || xn) || (y1 || ... || ~xi || ... || yn) = true
        Nothing -> collapsed
    fromSimplified =
      \case
        PBS.Inconsistent -> collapsed
        PBS.SinglePositive (EL.BoolExprWrapper e) -> pure e
        PBS.SingleNegative (EL.BoolExprWrapper e) -> notPred trueExpr falseExpr alloc e
        PBS.Merged pbs -> alloc (EL.OrPred pbs) Nothing
    -- Insert a single element into an existing OrPred
    insertIntoOrPred pol newElem unchanged =
      case PBS.insertIfNotPresent pol (EL.BoolExprWrapper newElem) of
        Nothing -> collapsed
        Just newPol ->
          if PBS.totalSize newPol == PBS.totalSize pol
          then pure unchanged
          else alloc (EL.OrPred newPol) Nothing
{-# INLINE orPred #-}

xorPred ::
  ( Eq (Expr t f BT.BaseBoolType)
  , HasBaseType (f (Expr t f))
  , EV.HasLogicViews f
  ) =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp. EL.LogicExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  IO (Expr t f BT.BaseBoolType)
xorPred trueExpr falseExpr alloc x y
    -- x `xor` y = not (x == y)
  | Config.normalizeXor = do
      eqResult <- eq trueExpr falseExpr alloc x y
      notPred trueExpr falseExpr alloc eqResult
    -- false `xor` y = y
    -- test: xor-false-left
  | isFalse x = pure y
    -- x `xor` false = x
    -- test: xor-false-right
  | isFalse y = pure x
    -- true `xor` y = not y
    -- test: xor-true-left
  | isTrue x = notPred trueExpr falseExpr alloc y
    -- x `xor` true = not x
    -- test: xor-true-right
  | isTrue y = notPred trueExpr falseExpr alloc x
    -- x `xor` x = false
    -- test: xor-idempotent
  | x == y = pure falseExpr
  | otherwise = alloc (EL.XorPred x y) Nothing
{-# INLINE xorPred #-}

ite ::
  ( AD.Abstractable tp
  , HasBaseType (f (Expr t f))
  , Eq (Expr t f tp)
  ) =>
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f BT.BaseBoolType ->
  Expr t f tp ->
  Expr t f tp ->
  IO (Expr t f tp)
ite alloc c t f
    -- ite true t f = t
    -- test: ite-true
    -- test: bvite-true
  | isTrue c = pure t
    -- ite false t f = f
    -- test: ite-false
    -- test: bvite-false
  | isFalse c = pure f
    -- ite c x x = x
    -- test: ite-same
    -- test: bvite-same
  | t == f = pure t
  | otherwise = alloc (EL.Ite c t f) (AD.avJoin (baseType t) (E.eAbsVal t) (E.eAbsVal f))
{-# INLINE ite #-}

itePred ::
  ( HasBaseType (f (Expr t f))
  , EV.HasLogicViews f
  , Eq (Expr t f BT.BaseBoolType)
  , Hashable (Expr t f BT.BaseBoolType)
  , PC.HashableF (f (Expr t f))
  ) =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  IO (Expr t f BT.BaseBoolType)
itePred trueExpr falseExpr alloc c t f
    -- ite c true false = c
    -- test: ite-bool-id
  | isTrue t, isFalse f = pure c
    -- ite c false true = not c
    -- test: ite-bool-not
  | isFalse t, isTrue f = notPred trueExpr falseExpr alloc c
    -- ite c c y = c || y
    -- test: ite-absorption-or
  | c == t = orPred trueExpr falseExpr alloc c f
    -- ite c x c = c && x
    -- test: ite-absorption-and
  | c == f = andPred trueExpr falseExpr alloc c t
    -- ite c true y = c || y
    -- test: ite-const-true-left
  | isTrue t = orPred trueExpr falseExpr alloc c f
    -- ite c false y = (not c) && y
    -- test: ite-const-false-right
  | isFalse t = do
      nc <- notPred trueExpr falseExpr alloc c
      andPred trueExpr falseExpr alloc nc f
    -- ite c x true = (not c) || x
  | isTrue f = do
      nc <- notPred trueExpr falseExpr alloc c
      orPred trueExpr falseExpr alloc nc t
    -- ite c x false = c && x
  | isFalse f = andPred trueExpr falseExpr alloc c t
    -- ite (not c) x y = ite c y x
  | Just nc <- EV.asNotPred c = ite alloc nc f t
  | otherwise = ite alloc c t f
{-# INLINE itePred #-}

-- Helper to get width of a bitvector expression
bvWidth' :: HasBaseType (f (Expr t f)) => Expr t f (BT.BaseBVType w) -> NatRepr w
bvWidth' e = case baseType e of BT.BaseBVRepr w -> w
{-# INLINE bvWidth' #-}

-- Helper to extract BV literal
asBVLit' :: HasBaseType (f (Expr t f)) => Expr t f (BT.BaseBVType w) -> Maybe (NatRepr w, BV.BV w)
asBVLit' e = case BVD.asSingleton (AD.getAbsValue e) of
  Just i -> Just (bvWidth' e, BV.mkBV (bvWidth' e) i)
  Nothing -> Nothing
{-# INLINE asBVLit' #-}

bvUlt ::
  (HasBaseType (f (Expr t f)), EV.HasBVViews f, Eq (Expr t f (BT.BaseBVType w))) =>
  1 <= w =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f BT.BaseBoolType)
bvUlt trueExpr falseExpr alloc x y
  -- x < x = false
  -- test: bvult-irrefl
  | x == y = pure falseExpr
  -- x < 0 = false
  -- test: bvult-zero
  | Just (_, yBV) <- asBVLit' y, yBV == BV.zero (bvWidth' y) = pure falseExpr
  -- maxUnsigned < x = false
  | Just (w, xBV) <- asBVLit' x, xBV == BV.maxUnsigned w = pure falseExpr
  -- Constant folding
  | Just (_, xBV) <- asBVLit' x
  , Just (_, yBV) <- asBVLit' y =
      pure $ if BV.ult xBV yBV then trueExpr else falseExpr
  | otherwise =
      alloc
        (EL.BVUlt (bvWidth' x) x y)
        (BVD.ult (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvUlt #-}

bvUle ::
  ( HasBaseType (f (Expr t f))
  , EV.HasBVViews f
  , EV.HasLogicViews f
  , Eq (Expr t f (BT.BaseBVType w))
  , Eq (Expr t f BT.BaseBoolType)
  , Hashable (Expr t f BT.BaseBoolType)
  , PC.HashableF (f (Expr t f))
  , AD.Abstractable (BT.BaseBVType w)
  ) =>
  1 <= w =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f BT.BaseBoolType)
bvUle trueExpr falseExpr alloc x y
  -- x <= y = (x < y) || (x == y)
  | Config.normalizeBVUle = do
      ltResult <- bvUlt trueExpr falseExpr alloc x y
      eqResult <- eq trueExpr falseExpr alloc x y
      orPred trueExpr falseExpr alloc ltResult eqResult
  -- x <= x = true
  -- test: bvule-refl
  | x == y = pure trueExpr
  -- 0 <= x = true
  | Just (_, xBV) <- asBVLit' x, xBV == BV.zero (bvWidth' x) = pure trueExpr
  -- x <= maxUnsigned = true
  | Just (w, yBV) <- asBVLit' y, yBV == BV.maxUnsigned w = pure trueExpr
  -- Constant folding
  | Just (_, xBV) <- asBVLit' x
  , Just (_, yBV) <- asBVLit' y =
      pure $ if BV.ule xBV yBV then trueExpr else falseExpr
  | otherwise =
      alloc
        (EL.BVUle (bvWidth' x) x y)
        (fmap not (BVD.ult (E.eAbsVal y) (E.eAbsVal x)))
{-# INLINE bvUle #-}

bvSlt ::
  (HasBaseType (f (Expr t f)), EV.HasBVViews f, Eq (Expr t f (BT.BaseBVType w))) =>
  1 <= w =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f BT.BaseBoolType)
bvSlt trueExpr falseExpr alloc x y
  -- x < x = false
  -- test: bvslt-irrefl
  | x == y = pure falseExpr
  -- Constant folding
  | Just (w, xBV) <- asBVLit' x
  , Just (_, yBV) <- asBVLit' y =
      pure $ if BV.slt w xBV yBV then trueExpr else falseExpr
  | otherwise =
      alloc
        (EL.BVSlt (bvWidth' x) x y)
        (BVD.slt (bvWidth' x) (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvSlt #-}

bvSle ::
  ( HasBaseType (f (Expr t f))
  , EV.HasBVViews f
  , EV.HasLogicViews f
  , Eq (Expr t f (BT.BaseBVType w))
  , Eq (Expr t f BT.BaseBoolType)
  , Hashable (Expr t f BT.BaseBoolType)
  , PC.HashableF (f (Expr t f))
  , AD.Abstractable (BT.BaseBVType w)
  ) =>
  1 <= w =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f BT.BaseBoolType)
bvSle trueExpr falseExpr alloc x y
  -- x <=s y = (x <s y) || (x == y)
  | Config.normalizeBVSle = do
      sltResult <- bvSlt trueExpr falseExpr alloc x y
      eqResult <- eq trueExpr falseExpr alloc x y
      orPred trueExpr falseExpr alloc sltResult eqResult
  -- x <= x = true
  -- test: bvsle-refl
  | x == y = pure trueExpr
  -- Constant folding
  | Just (w, xBV) <- asBVLit' x
  , Just (_, yBV) <- asBVLit' y =
      pure $ if BV.sle w xBV yBV then trueExpr else falseExpr
  -- x <= y iff not (y < x)
  | otherwise =
      alloc
        (EL.BVSle (bvWidth' x) x y)
        (fmap not (BVD.slt (bvWidth' x) (E.eAbsVal y) (E.eAbsVal x)))
{-# INLINE bvSle #-}

bvIsNonzero ::
  ( HasBaseType (f (Expr t f))
  , EV.HasBVViews f
  , EV.HasLogicViews f
  , Eq (Expr t f (BT.BaseBVType w))
  , AD.Abstractable (BT.BaseBVType w)
  ) =>
  1 <= w =>
  Expr t f BT.BaseBoolType ->
  Expr t f BT.BaseBoolType ->
  (forall tp'. EL.LogicExpr (Expr t f) tp' -> AD.AbstractValue tp' -> IO (Expr t f tp')) ->
  (NatRepr w -> BV.BV w -> IO (Expr t f (BT.BaseBVType w))) -> -- bvLit function
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f BT.BaseBoolType)
bvIsNonzero trueExpr falseExpr alloc bvLitFn x
  -- isNonzero(0) = false
  | Just (_, bv) <- asBVLit' x, bv == BV.zero (bvWidth' x) = pure falseExpr
  -- isNonzero(c) = c != 0 (constant folding)
  | Just (_, bv) <- asBVLit' x = pure $ if bv /= BV.zero (bvWidth' x) then trueExpr else falseExpr
  -- Implemented as not (x == 0)
  | otherwise = do
      let w = bvWidth' x
      zero <- bvLitFn w (BV.zero w)
      eqResult <- eq trueExpr falseExpr alloc zero x
      notPred trueExpr falseExpr alloc eqResult
{-# INLINE bvIsNonzero #-}
