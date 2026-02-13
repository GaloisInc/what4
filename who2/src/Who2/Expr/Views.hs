{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Expr.Views
  ( HasLogicViews(..)
  , HasBVViews(..)
  ) where

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.NatRepr (type (<=), NatRepr)

import qualified What4.BaseTypes as BT
import qualified What4.SemiRing as SR

import qualified Who2.Expr as E
import qualified Who2.Expr.Bloom.Polarized as PBS
import qualified Who2.Expr.SemiRing.Product as SRP
import qualified Who2.Expr.SemiRing.Sum as SRS

-- | Typeclass for inspecting logical structure of expressions.
-- This allows us to implement rewrites without creating import cycles.
class HasLogicViews f where
  -- | View: is this (not x)? Returns x if so.
  asNotPred :: E.Expr t f BT.BaseBoolType -> Maybe (E.Expr t f BT.BaseBoolType)

  -- | View: is this an AndPred? Returns the polarized bloom sequence.
  asAndPred :: E.Expr t f BT.BaseBoolType -> Maybe (PBS.PolarizedBloomSeq (E.Expr t f BT.BaseBoolType))

  -- | View: is this an OrPred? Returns the polarized bloom sequence.
  asOrPred :: E.Expr t f BT.BaseBoolType -> Maybe (PBS.PolarizedBloomSeq (E.Expr t f BT.BaseBoolType))

  -- | View: is this (ite c t f)? Returns (c, t, f) if so.
  asIte :: E.Expr t f BT.BaseBoolType -> Maybe (E.Expr t f BT.BaseBoolType, E.Expr t f BT.BaseBoolType, E.Expr t f BT.BaseBoolType)

-- | Typeclass for inspecting bitvector structure of expressions.
class HasBVViews f where
  -- | View: is this a BVLit?
  asBVLit :: (1 <= w) => E.Expr t f (BT.BaseBVType w) -> Maybe (NatRepr w, BV.BV w)

  -- | View: is this BVNotBits?
  asBVNotBits :: (1 <= w) => E.Expr t f (BT.BaseBVType w) -> Maybe (E.Expr t f (BT.BaseBVType w))

  -- | View: is this BVNeg? Returns the argument if so.
  asBVNeg :: (1 <= w) => E.Expr t f (BT.BaseBVType w) -> Maybe (E.Expr t f (BT.BaseBVType w))

  -- | View: is this BVAdd? Returns the weighted sum.
  asBVAdd :: (1 <= w) => E.Expr t f (BT.BaseBVType w) -> Maybe (SRS.SRSum (SR.SemiRingBV SR.BVArith w) (E.Expr t f))

  -- | View: is this BVMul? Returns the product.
  asBVMul :: (1 <= w) => E.Expr t f (BT.BaseBVType w) -> Maybe (SRP.SRProd (SR.SemiRingBV SR.BVBits w) (E.Expr t f))

  -- | View: is this BVAndBits? Returns the polarized bloom sequence.
  asBVAndBits :: (1 <= w) => E.Expr t f (BT.BaseBVType w) -> Maybe (PBS.PolarizedBloomSeq (E.Expr t f (BT.BaseBVType w)))

  -- | View: is this BVOrBits? Returns the polarized bloom sequence.
  asBVOrBits :: (1 <= w) => E.Expr t f (BT.BaseBVType w) -> Maybe (PBS.PolarizedBloomSeq (E.Expr t f (BT.BaseBVType w)))
