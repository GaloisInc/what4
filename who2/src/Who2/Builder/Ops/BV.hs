{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Builder.Ops.BV
  ( bvLit
  , bvAdd
  , bvNeg
  , bvSub
  , bvMul
  , bvAndBits
  , bvOrBits
  , bvXorBits
  , bvNotBits
  , bvConcat
  , bvSelect
  , bvZext
  , bvSext
  , bvShl
  , bvLshr
  , bvAshr
  , bvUdiv
  , bvUrem
  , bvSdiv
  , bvSrem
  , bvRol
  , bvRor
  ) where

import qualified Data.BitVector.Sized as BV

import           Data.Parameterized.NatRepr (type (<=), type (+), NatRepr, addNat, LeqProof(LeqProof), leqAddPos, withLeqProof, leqTrans, knownNat)
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Classes as PC

import qualified What4.BaseTypes as BT
import qualified What4.SemiRing as SR
import qualified What4.Utils.AbstractDomains as AD
import qualified What4.Utils.BVDomain as BVD

import Data.Coerce (coerce)
import Data.Hashable (Hashable)

import Who2.Expr (Expr, HasBaseType)
import qualified Who2.Expr as E
import qualified Who2.Expr.SemiRing.Product as SRP
import qualified Who2.Expr.SemiRing.Sum as SRS
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr.Views as EV
import qualified Who2.Expr.Bloom.Polarized as PBS

asInteger :: Expr t f (BT.BaseBVType w) -> Maybe Integer
asInteger = BVD.asSingleton . AD.getAbsValue
{-# INLINE asInteger #-}

asBVLit :: HasBaseType (f (Expr t f)) => Expr t f (BT.BaseBVType w) -> Maybe (NatRepr w, BV.BV w)
asBVLit e = case E.eApp e of
  _ -> case asInteger e of
    Just i -> Just (EBV.width e, BV.mkBV (EBV.width e) i)
    Nothing -> Nothing
{-# INLINE asBVLit #-}

isZero :: Expr t f (BT.BaseBVType w) -> Bool
isZero = (== Just 0) . asInteger
{-# INLINE isZero #-}

isOne :: Expr t f (BT.BaseBVType w) -> Bool
isOne = (== Just 1) . asInteger
{-# INLINE isOne #-}

-- | Check if this is all ones (maxBound)
isAllOnes :: HasBaseType (f (Expr t f)) => Expr t f (BT.BaseBVType w) -> Bool
isAllOnes e = case asBVLit e of
  Just (w, bv) -> bv == BV.maxUnsigned w
  Nothing -> False
{-# INLINE isAllOnes #-}

bvLit ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  NatRepr w ->
  BV.BV w ->
  IO (Expr t f (BT.BaseBVType w))
bvLit alloc w bv =
  alloc (EBV.BVLit w bv) (BVD.singleton w (BV.asUnsigned bv))
{-# INLINE bvLit #-}

bvAdd ::
  (HasBaseType (f (Expr t f)), Eq (Expr t f (BT.BaseBVType w)), Ord (Expr t f (BT.BaseBVType w)), Hashable (Expr t f (BT.BaseBVType w)), PC.HashableF (Expr t f), PC.OrdF (Expr t f), EV.HasBVViews f) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvAdd alloc x y
  -- 0 + y = y
  -- test: bvadd-zero-left
  | isZero x = pure y
  -- x + 0 = x
  -- test: bvadd-zero-right
  | isZero y = pure x
  -- (x_ws) + (y_ws) = merge weighted sums
  -- test: bvadd-commutative
  | Just xWs <- EV.asBVAdd x
  , Just yWs <- EV.asBVAdd y =
      buildBVAdd alloc x y (SRS.add xWs yWs)
  -- (x_ws) + c = add constant to weighted sum offset
  -- test: bvadd-combine-constants
  | Just xWs <- EV.asBVAdd x
  , Just (_, c) <- asBVLit y =
      buildBVAdd alloc x y (SRS.addConstant xWs c)
  -- c + (y_ws) = add constant to weighted sum offset
  -- test: bvadd-combine-constants-left
  | Just (_, c) <- asBVLit x
  , Just yWs <- EV.asBVAdd y =
      buildBVAdd alloc x y (SRS.addConstant yWs c)
  -- (x_ws) + y = add variable to weighted sum
  | Just xWs <- EV.asBVAdd x =
      buildBVAdd alloc x y (SRS.addVar xWs y)
  -- x + (y_ws) = add variable to weighted sum
  | Just yWs <- EV.asBVAdd y =
      buildBVAdd alloc x y (SRS.addVar yWs x)
  -- c1 + c2 = fold constants
  -- test: bvadd-const-simplify
  | Just (w, c1) <- asBVLit x
  , Just (_, c2) <- asBVLit y =
      bvLit alloc w (BV.add w c1 c2)
  -- x + c = create weighted sum with offset
  | Just (_, c) <- asBVLit y =
      let w = EBV.width x
          sr = SR.SemiRingBVRepr SR.BVArithRepr w
      in buildBVAdd alloc x y (SRS.affineVar sr (BV.one w) x c)
  -- c + y = create weighted sum with offset
  | Just (_, c) <- asBVLit x =
      let w = EBV.width y
          sr = SR.SemiRingBVRepr SR.BVArithRepr w
      in buildBVAdd alloc x y (SRS.affineVar sr (BV.one w) y c)
  -- x + y = create weighted sum with two variables
  | otherwise =
      let w = EBV.width x
          sr = SR.SemiRingBVRepr SR.BVArithRepr w
          x' = E.minByHash x y
          y' = E.maxByHash x y
          ws = SRS.add (SRS.var sr x') (SRS.var sr y')
      in buildBVAdd alloc x y ws
  where
    buildBVAdd ::
      forall w' t' f'.
      (HasBaseType (f' (Expr t' f')), Eq (Expr t' f' (BT.BaseBVType w')), Ord (Expr t' f' (BT.BaseBVType w')), Hashable (Expr t' f' (BT.BaseBVType w')), PC.HashableF (Expr t' f'), PC.OrdF (Expr t' f'), EV.HasBVViews f', 1 <= w') =>
      (forall tp. EBV.BVExpr (Expr t' f') tp -> AD.AbstractValue tp -> IO (Expr t' f' tp)) ->
      Expr t' f' (BT.BaseBVType w') ->
      Expr t' f' (BT.BaseBVType w') ->
      SRS.SRSum (SR.SemiRingBV SR.BVArith w') (Expr t' f') ->
      IO (Expr t' f' (BT.BaseBVType w'))
    buildBVAdd alloc' x' y' ws =
      let w = EBV.width x'
      in case SRS.asConstant ws of
           Just c -> bvLit alloc' w c
           Nothing -> alloc'
                        (EBV.BVAdd w ws)
                        (BVD.add (E.eAbsVal x') (E.eAbsVal y'))
{-# INLINE bvAdd #-}

bvNeg ::
  (HasBaseType (f (Expr t f)), EV.HasBVViews f) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvNeg alloc x
  -- -(0) = 0
  -- test: bvneg-zero
  | isZero x = pure x
  -- Constant folding
  -- test: bvneg-const
  | Just (w, bv) <- asBVLit x = bvLit alloc w (BV.negate w bv)
  -- -(-y) = y
  -- test: bvneg-double
  | Just inner <- EV.asBVNeg x = pure inner
  | otherwise =
      alloc
        (EBV.BVNeg (EBV.width x) x)
        (BVD.negate (E.eAbsVal x))
{-# INLINE bvNeg #-}

bvSub ::
  ( Eq (f (Expr t f) (BT.BaseBVType w))
  , Ord (f (Expr t f) (BT.BaseBVType w))
  , Hashable (Expr t f (BT.BaseBVType w))
  , HasBaseType (f (Expr t f))
  , PC.HashableF (Expr t f)
  , PC.OrdF (Expr t f)
  , EV.HasBVViews f
  ) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvSub alloc x y
  -- x - 0 = x
  -- test: bvsub-zero
  | isZero y = pure x
  -- 0 - x = -x
  -- test: bvsub-as-neg
  | isZero x = bvNeg alloc y
  -- x - x = 0
  -- test: bvsub-self
  | x == y = bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
  -- x - c = x + (-c)
  | Just (w, bv) <- asBVLit y = bvAdd alloc x =<< bvLit alloc w (BV.negate w bv)
  | otherwise =
      alloc
        (EBV.BVSub (EBV.width x) x y)
        (BVD.add (E.eAbsVal x) (BVD.negate (E.eAbsVal y)))
{-# INLINE bvSub #-}

bvMul ::
  (HasBaseType (f (Expr t f)), Eq (Expr t f (BT.BaseBVType w)), Ord (Expr t f (BT.BaseBVType w)), Hashable (Expr t f (BT.BaseBVType w)), EV.HasBVViews f) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvMul alloc x y
  -- 0 * y = 0
  -- test: bvmul-zero-left
  | isZero x = pure x
  -- x * 0 = 0
  -- test: bvmul-zero-right
  | isZero y = pure y
  -- 1 * y = y
  -- test: bvmul-one-left
  | isOne x = pure y
  -- x * 1 = x
  -- test: bvmul-one-right
  | isOne y = pure x
  -- (x_prod) * (y_prod) = merge products
  -- test: bvmul-exponent-combine
  | Just xProd <- EV.asBVMul x
  , Just yProd <- EV.asBVMul y =
      buildBVMul alloc x y (SRP.mul xProd yProd)
  -- (x_prod) * c = scale product coefficient
  -- test: bvmul-scale-right
  | Just xProd <- EV.asBVMul x
  , Just (_, c) <- asBVLit y =
      buildBVMul alloc x y (SRP.scale xProd c)
  -- c * (y_prod) = scale product coefficient
  -- test: bvmul-scale-left
  | Just (_, c) <- asBVLit x
  , Just yProd <- EV.asBVMul y =
      buildBVMul alloc x y (SRP.scale yProd c)
  -- (x_prod) * y = multiply product by variable
  | Just xProd <- EV.asBVMul x =
      buildBVMul alloc x y (SRP.mulVar xProd y)
  -- x * (y_prod) = multiply product by variable
  | Just yProd <- EV.asBVMul y =
      buildBVMul alloc x y (SRP.mulVar yProd x)
  -- c1 * c2 = fold constants
  -- test: bvmul-const
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.mul wx bvx bvy)
  -- x * y = create product
  -- test: bvmul-commutative
  | otherwise =
      let w = EBV.width x
          sr = SR.SemiRingBVRepr SR.BVBitsRepr w
          x' = E.minByHash x y
          y' = E.maxByHash x y
          wp = SRP.mul (SRP.var sr x') (SRP.var sr y')
      in buildBVMul alloc x y wp
  where
    buildBVMul ::
      forall w' t' f'.
      (HasBaseType (f' (Expr t' f')), 1 <= w') =>
      (forall tp. EBV.BVExpr (Expr t' f') tp -> AD.AbstractValue tp -> IO (Expr t' f' tp)) ->
      Expr t' f' (BT.BaseBVType w') ->
      Expr t' f' (BT.BaseBVType w') ->
      SRP.SRProd (SR.SemiRingBV SR.BVBits w') (Expr t' f') ->
      IO (Expr t' f' (BT.BaseBVType w'))
    buildBVMul alloc' x' y' wp =
      let w = EBV.width x'
      in case SRP.asConstant wp of
           Just c -> bvLit alloc' w c
           Nothing -> alloc'
                        (EBV.BVMul w wp)
                        (BVD.mul (E.eAbsVal x') (E.eAbsVal y'))
{-# INLINE bvMul #-}

bvAndBits ::
  ( Eq (f (Expr t f) (BT.BaseBVType w))
  , HasBaseType (f (Expr t f))
  , EV.HasBVViews f
  , Hashable (Expr t f (BT.BaseBVType w))
  , PC.HashableF (f (Expr t f))
  ) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvAndBits alloc x y
  -- 0 & y = 0
  -- test: bvand-zero-left
  | isZero x = pure x
  -- x & 0 = 0
  -- test: bvand-zero-right
  | isZero y = pure y
  -- ~0 & y = y
  -- test: bvand-ones-left
  | isAllOnes x = pure y
  -- x & ~0 = x
  -- test: bvand-ones-right
  | isAllOnes y = pure x
  -- x & x = x
  -- test: bvand-idem
  | x == y = pure x
  -- x & (~x) = 0
  | Just nx <- EV.asBVNotBits y, x == nx =
      bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
  | Just nx <- EV.asBVNotBits x, nx == y =
      bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
  -- Constant folding
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.and bvx bvy)
  -- (x1 & ... & xn) & (y1 & ... & yn) = x1 & ... & xn & y1 & ... & yn
  | Just xs <- EV.asBVAndBits x
  , Just ys <- EV.asBVAndBits y = fromMerged (PBS.merge (coerce xs) (coerce ys))
  -- (x1 & ... & xn) & y = x1 & ... & xn & y
  | Just xs <- EV.asBVAndBits x = insertIntoBVAndBits (coerce xs) y x
  -- x & (y1 & ... & yn) = y1 & ... & yn & x
  | Just ys <- EV.asBVAndBits y = insertIntoBVAndBits (coerce ys) x y
  | otherwise =
      let x' = E.minByHash x y
          y' = E.maxByHash x y
      in fromSimplified (PBS.fromTwo (EBV.BVExprWrapper x') (EBV.BVExprWrapper y'))
  where
    collapsed = bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
    newAbsVal = BVD.and (E.eAbsVal x) (E.eAbsVal y)
    fromMerged =
      \case
        Just pbs -> alloc (EBV.BVAndBits (EBV.width x) pbs) newAbsVal
        -- (x1 & ... & xn) & (y1 & ... & ~xi & ... & yn) = false
        Nothing -> collapsed
    fromSimplified =
      \case
        PBS.Inconsistent -> collapsed
        PBS.SinglePositive (EBV.BVExprWrapper e) -> pure e
        PBS.SingleNegative (EBV.BVExprWrapper e) -> bvNotBits alloc e
        PBS.Merged pbs -> alloc (EBV.BVAndBits (EBV.width x) pbs) newAbsVal
    -- Insert a single element into an existing BVAndBits
    insertIntoBVAndBits pol newElem unchanged =
      case PBS.insertIfNotPresent pol (EBV.BVExprWrapper newElem) of
        Nothing -> collapsed
        Just newPol ->
          if PBS.totalSize newPol == PBS.totalSize pol
          then pure unchanged
          else alloc (EBV.BVAndBits (EBV.width unchanged) newPol) newAbsVal
{-# INLINE bvAndBits #-}

bvOrBits ::
  ( Eq (f (Expr t f) (BT.BaseBVType w))
  , HasBaseType (f (Expr t f))
  , EV.HasBVViews f
  , Hashable (Expr t f (BT.BaseBVType w))
  , PC.HashableF (f (Expr t f))
  ) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvOrBits alloc x y
  -- 0 | y = y
  -- test: bvor-zero-left
  | isZero x = pure y
  -- x | 0 = x
  -- test: bvor-zero-right
  | isZero y = pure x
  -- ~0 | y = ~0
  -- test: bvor-ones-left
  | isAllOnes x = pure x
  -- x | ~0 = ~0
  -- test: bvor-ones-right
  | isAllOnes y = pure y
  -- x | x = x
  -- test: bvor-idem
  | x == y = pure x
  -- x | (~x) = ~0
  | Just nx <- EV.asBVNotBits y, x == nx =
      bvLit alloc (EBV.width x) (BV.maxUnsigned (EBV.width x))
  | Just nx <- EV.asBVNotBits x, nx == y =
      bvLit alloc (EBV.width x) (BV.maxUnsigned (EBV.width x))
  -- Constant folding
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.or bvx bvy)
  -- (x1 | ... | xn) | (y1 | ... | yn) = x1 | ... | xn | y1 | ... | yn
  | Just xPol <- EV.asBVOrBits x
  , Just yPol <- EV.asBVOrBits y = fromMerged (PBS.merge (coerce xPol) (coerce yPol))
  -- (x1 | ... | xn) | y = x1 | ... | xn | y
  | Just xPol <- EV.asBVOrBits x = insertIntoBVOrBits (coerce xPol) y x
  -- x | (y1 | ... | yn) = y1 | ... | yn | x
  | Just yPol <- EV.asBVOrBits y = insertIntoBVOrBits (coerce yPol) x y
  | otherwise =
      let x' = E.minByHash x y
          y' = E.maxByHash x y
      in fromSimplified (PBS.fromTwo (EBV.BVExprWrapper x') (EBV.BVExprWrapper y'))
  where
    collapsed = bvLit alloc (EBV.width x) (BV.maxUnsigned (EBV.width x))
    newAbsVal = BVD.or (E.eAbsVal x) (E.eAbsVal y)
    fromMerged =
      \case
        Just pbs -> alloc (EBV.BVOrBits (EBV.width x) pbs) newAbsVal
        -- (x1 | ... | xn) | (y1 | ... | ~xi | ... | yn) = true
        Nothing -> collapsed
    fromSimplified =
      \case
        PBS.Inconsistent -> collapsed
        PBS.SinglePositive (EBV.BVExprWrapper e) -> pure e
        PBS.SingleNegative (EBV.BVExprWrapper e) -> bvNotBits alloc e
        PBS.Merged pbs -> alloc (EBV.BVOrBits (EBV.width x) pbs) newAbsVal
    -- Insert a single element into an existing BVOrBits
    insertIntoBVOrBits pol newElem unchanged =
      case PBS.insertIfNotPresent pol (EBV.BVExprWrapper newElem) of
        Nothing -> collapsed
        Just newPol ->
          if PBS.totalSize newPol == PBS.totalSize pol
          then pure unchanged
          else alloc (EBV.BVOrBits (EBV.width unchanged) newPol) newAbsVal
{-# INLINE bvOrBits #-}

bvXorBits ::
  ( Eq (f (Expr t f) (BT.BaseBVType w))
  , HasBaseType (f (Expr t f))
  , EV.HasBVViews f
  ) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvXorBits alloc x y
  -- 0 ^ y = y
  -- test: bvxor-zero-left
  | isZero x = pure y
  -- x ^ 0 = x
  -- test: bvxor-zero-right
  | isZero y = pure x
  -- x ^ x = 0
  -- test: bvxor-self
  | x == y = bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
  -- x ^ ~0 = ~x
  | isAllOnes x = bvNotBits alloc y
  | isAllOnes y = bvNotBits alloc x
  -- Constant folding
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.xor bvx bvy)
  | otherwise =
      let x' = E.minByHash x y
          y' = E.maxByHash x y
      in alloc
           (EBV.BVXorBits (EBV.width x) x' y')
           (BVD.xor (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvXorBits #-}

bvNotBits ::
  (HasBaseType (f (Expr t f)), EV.HasBVViews f) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvNotBits alloc x
  -- Constant folding
  | Just (w, bv) <- asBVLit x = bvLit alloc w (BV.complement w bv)
  -- ~~x = x
  -- test: bvnot-double
  | Just inner <- EV.asBVNotBits x = pure inner
  | otherwise =
      alloc
        (EBV.BVNotBits (EBV.width x) x)
        (BVD.not (E.eAbsVal x))
{-# INLINE bvNotBits #-}

bvConcat ::
  HasBaseType (f (Expr t f)) =>
  (1 <= w, 1 <= w') =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w') ->
  IO (Expr t f (BT.BaseBVType (w + w')))
bvConcat alloc x y =
  let wx = EBV.width x
      wy = EBV.width y
  in withLeqProof (leqAddPos wx wy) $
    -- Constant folding
    -- test: bvconcat-const
    if | Just (_, bvx) <- asBVLit x
       , Just (_, bvy) <- asBVLit y ->
           bvLit alloc (addNat wx wy) (BV.concat wx wy bvx bvy)
       | otherwise ->
           alloc
             (EBV.BVConcat wx wy x y)
             (BVD.concat wx (E.eAbsVal x) wy (E.eAbsVal y))
{-# INLINE bvConcat #-}

bvSelect ::
  HasBaseType (f (Expr t f)) =>
  (1 <= n, i + n <= w) =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  NatRepr i ->
  NatRepr n ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType n))
bvSelect alloc i n x
  -- Constant folding
  -- test: bvselect-const
  | Just (_, bv) <- asBVLit x =
      bvLit alloc n (BV.select i n bv)
  -- Full selection is identity: select 0 w x = x
  | Just NR.Refl <- NR.testEquality i (NR.knownNat @0)
  , Just NR.Refl <- NR.testEquality n (EBV.width x) =
      pure x
  | otherwise =
      alloc
        (EBV.BVSelect i n (EBV.width x) x)
        (BVD.select i n (E.eAbsVal x))
{-# INLINE bvSelect #-}

bvZext ::
  forall f t w w'.
  HasBaseType (f (Expr t f)) =>
  (1 <= w, w + 1 <= w') =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  NatRepr w' ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w'))
bvZext alloc w' x =
  let wx = EBV.width x in
  -- Prove 1 <= w' from 1 <= w + 1 and w + 1 <= w'
  withLeqProof (leqTrans (leqAddPos wx (knownNat @1)) (LeqProof :: LeqProof (w + 1) w')) $
    -- Constant folding
    -- test: bvzext-const
    if | Just (_, bv) <- asBVLit x ->
           bvLit alloc w' (BV.zext w' bv)
       | otherwise ->
           alloc
             (EBV.BVZext w' wx x)
             (BVD.zext (E.eAbsVal x) w')
{-# INLINE bvZext #-}

bvSext ::
  forall f t w w'.
  HasBaseType (f (Expr t f)) =>
  (1 <= w, w + 1 <= w') =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  NatRepr w' ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w'))
bvSext alloc w' x =
  let wx = EBV.width x in
  -- Prove 1 <= w' from 1 <= w + 1 and w + 1 <= w'
  withLeqProof (leqTrans (leqAddPos wx (knownNat @1)) (LeqProof :: LeqProof (w + 1) w')) $
    -- Constant folding
    -- test: bvsext-const
    if | Just (_, bv) <- asBVLit x ->
           bvLit alloc w' (BV.sext wx w' bv)
       | otherwise ->
           alloc
             (EBV.BVSext w' wx x)
             (BVD.sext wx (E.eAbsVal x) w')
{-# INLINE bvSext #-}

bvShl ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvShl alloc x y
  -- x << 0 = x
  -- test: bvshl-zero
  | isZero y = pure x
  -- 0 << n = 0
  | isZero x = pure x
  -- shift amount >= width
  -- test: bvshl-by-width
  | Just (w, shamt) <- asBVLit y
  , BV.asUnsigned shamt >= NR.intValue w =
      bvLit alloc w (BV.zero w)
  -- Constant folding
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.shl wx bvx (fromInteger (BV.asUnsigned bvy)))
  | otherwise =
      alloc
        (EBV.BVShl (EBV.width x) x y)
        (BVD.shl (EBV.width x) (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvShl #-}

bvLshr ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvLshr alloc x y
  -- x >> 0 = x
  -- test: bvlshr-zero
  | isZero y = pure x
  -- 0 >> n = 0
  | isZero x = pure x
  -- shift amount >= width
  | Just (w, shamt) <- asBVLit y
  , BV.asUnsigned shamt >= NR.intValue w =
      bvLit alloc w (BV.zero w)
  -- Constant folding
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.lshr wx bvx (fromInteger (BV.asUnsigned bvy)))
  | otherwise =
      alloc
        (EBV.BVLshr (EBV.width x) x y)
        (BVD.lshr (EBV.width x) (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvLshr #-}

bvAshr ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvAshr alloc x y
  -- x >> 0 = x
  -- test: bvashr-zero
  | isZero y = pure x
  -- 0 >> n = 0
  | isZero x = pure x
  -- Constant folding
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.ashr wx bvx (fromInteger (BV.asUnsigned bvy)))
  | otherwise =
      alloc
        (EBV.BVAshr (EBV.width x) x y)
        (BVD.ashr (EBV.width x) (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvAshr #-}

bvUdiv ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvUdiv alloc x y
  -- x / 1 = x
  -- test: bvudiv-one
  | isOne y = pure x
  -- 0 / x = 0
  -- test: bvudiv-zero
  | isZero x = pure x
  -- Constant folding
  -- test: bvudiv-const
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y
  , BV.asUnsigned bvy /= 0 =
      bvLit alloc wx (BV.uquot bvx bvy)
  | otherwise =
      alloc
        (EBV.BVUdiv (EBV.width x) x y)
        (BVD.udiv (E.eAbsVal x) (BVD.union (BVD.singleton (EBV.width y) 1) (E.eAbsVal y)))
{-# INLINE bvUdiv #-}

bvUrem ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvUrem alloc x y
  -- x % 1 = 0
  -- test: bvurem-one
  | isOne y = bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
  -- Constant folding
  -- test: bvurem-const
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y
  , BV.asUnsigned bvy /= 0 =
      bvLit alloc wx (BV.urem bvx bvy)
  -- if x < y (unsigned), return x
  -- test: bvurem-small
  | Just True <- BVD.ult (E.eAbsVal x) (E.eAbsVal y) = pure x
  | otherwise =
      alloc
        (EBV.BVUrem (EBV.width x) x y)
        (BVD.urem (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvUrem #-}

bvSdiv ::
  (HasBaseType (f (Expr t f)), EV.HasBVViews f) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvSdiv alloc x y
  -- x / 1 = x
  -- test: bvsdiv-one
  | isOne y = pure x
  -- 0 / x = 0
  | isZero x = pure x
  -- x / -1 = -x
  -- test: bvsdiv-neg-one
  | Just (w, bv) <- asBVLit y
  , bv == BV.maxUnsigned w =
      bvNeg alloc x
  -- Constant folding
  -- test: bvsdiv-const
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y
  , BV.asUnsigned bvy /= 0 =
      bvLit alloc wx (BV.squot wx bvx bvy)
  | otherwise =
      alloc
        (EBV.BVSdiv (EBV.width x) x y)
        (BVD.sdiv (EBV.width x) (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvSdiv #-}

bvSrem ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvSrem alloc x y
  -- x % 1 = 0
  -- test: bvsrem-one
  | isOne y = bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
  -- x % -1 = 0
  | Just (w, bv) <- asBVLit y
  , bv == BV.maxUnsigned w =
      bvLit alloc (EBV.width x) (BV.zero (EBV.width x))
  -- Constant folding
  -- test: bvsrem-const
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y
  , BV.asUnsigned bvy /= 0 =
      bvLit alloc wx (BV.srem wx bvx bvy)
  | otherwise =
      alloc
        (EBV.BVSrem (EBV.width x) x y)
        (BVD.srem (EBV.width x) (E.eAbsVal x) (E.eAbsVal y))
{-# INLINE bvSrem #-}

bvRol ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvRol alloc x y
  -- Constant folding
  -- test: bvrol-const
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.rotateL wx bvx (fromInteger (BV.asUnsigned bvy)))
  -- Normalize rotation amount modulo width
  | otherwise = do
      let w = EBV.width x
      -- Compute y' = y % w to normalize rotation amount
      -- test: bvrol-width
      y' <- bvUrem alloc y =<< bvLit alloc w (BV.mkBV w (NR.intValue w))
      -- Check if rotation amount is zero after normalization
      -- test: bvrol-zero
      if isZero y'
        then pure x
        else alloc
               (EBV.BVRol w x y')
               (BVD.rol w (E.eAbsVal x) (E.eAbsVal y'))
{-# INLINE bvRol #-}

bvRor ::
  HasBaseType (f (Expr t f)) =>
  1 <= w =>
  (forall tp. EBV.BVExpr (Expr t f) tp -> AD.AbstractValue tp -> IO (Expr t f tp)) ->
  Expr t f (BT.BaseBVType w) ->
  Expr t f (BT.BaseBVType w) ->
  IO (Expr t f (BT.BaseBVType w))
bvRor alloc x y
  -- Constant folding
  -- test: bvror-const
  | Just (wx, bvx) <- asBVLit x
  , Just (_, bvy) <- asBVLit y =
      bvLit alloc wx (BV.rotateR wx bvx (fromInteger (BV.asUnsigned bvy)))
  -- Normalize rotation amount modulo width
  | otherwise = do
      let w = EBV.width x
      -- Compute y' = y % w to normalize rotation amount
      -- test: bvror-width
      y' <- bvUrem alloc y =<< bvLit alloc w (BV.mkBV w (NR.intValue w))
      -- Check if rotation amount is zero after normalization
      -- test: bvror-zero
      if isZero y'
        then pure x
        else alloc
               (EBV.BVRor w x y')
               (BVD.ror w (E.eAbsVal x) (E.eAbsVal y'))
{-# INLINE bvRor #-}
