{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Who2.Expr.BV
  ( BVExpr(..)
  , BVExprWrapper(..)
  , width
  , asBVNotBits
  ) where

import Data.Kind (Type)
import Data.Hashable (hashWithSalt)

import qualified Data.BitVector.Sized as BV

import qualified Data.Parameterized.Classes as PC
import           Data.Parameterized.NatRepr (type (<=), type (+), NatRepr, addNat)
import qualified Data.Parameterized.TH.GADT as PTH

import qualified What4.BaseTypes as BT

import qualified What4.SemiRing as SR

import Who2.Expr (Expr, HasBaseType(baseType))
import qualified Who2.Expr as E
import qualified Who2.Expr.BloomKv as BKv
import qualified Who2.Expr.PolarizedBloomSeq as PBS
import qualified Who2.Expr.Views as EV
import qualified Who2.Expr.SemiRing.Product as SRP
import qualified Who2.Expr.SemiRing.Sum as SRS

-- | 'Polarizable' wrapper for bitvector expressions used in both 'BVAndBits' and 'BVOrBits'
newtype BVExprWrapper f w = BVExprWrapper { unBVExprWrapper :: f (BT.BaseBVType w) }

data BVExpr (f :: BT.BaseType -> Type) (tp :: BT.BaseType) where
  BVLit ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(BV.BV w) ->
    BVExpr f (BT.BaseBVType w)

  BVAdd ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(SRS.SRSum (SR.SemiRingBV SR.BVArith w) f) ->
    BVExpr f (BT.BaseBVType w)

  BVNeg ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVSub ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVMul ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(SRP.SRProd (SR.SemiRingBV SR.BVBits w) f) ->
    BVExpr f (BT.BaseBVType w)

  BVAndBits ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(PBS.PolarizedBloomSeq (BVExprWrapper f w)) ->
    BVExpr f (BT.BaseBVType w)

  BVOrBits ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(PBS.PolarizedBloomSeq (BVExprWrapper f w)) ->
    BVExpr f (BT.BaseBVType w)

  BVXorBits ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVNotBits ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVConcat ::
    (1 <= w, 1 <= w', 1 <= w + w') =>
    !(NatRepr w) ->
    !(NatRepr w') ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w')) ->
    BVExpr f (BT.BaseBVType (w + w'))

  BVSelect ::
    (1 <= n, i + n <= w) =>
    !(NatRepr i) ->
    !(NatRepr n) ->
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType n)

  BVZext ::
    (1 <= w, 1 <= w', w + 1 <= w') =>
    !(NatRepr w') ->
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w')

  BVSext ::
    (1 <= w, 1 <= w', w + 1 <= w') =>
    !(NatRepr w') ->
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w')

  BVShl ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVLshr ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVAshr ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVUdiv ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVUrem ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVSdiv ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVSrem ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVRol ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVRor ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

instance HasBaseType (BVExpr f) where
  baseType =
    \case
      BVLit w _ -> BT.BaseBVRepr w
      BVAdd w _ -> BT.BaseBVRepr w
      BVNeg w _ -> BT.BaseBVRepr w
      BVSub w _ _ -> BT.BaseBVRepr w
      BVMul w _ -> BT.BaseBVRepr w
      BVAndBits w _ -> BT.BaseBVRepr w
      BVOrBits w _ -> BT.BaseBVRepr w
      BVXorBits w _ _ -> BT.BaseBVRepr w
      BVNotBits w _ -> BT.BaseBVRepr w
      BVConcat w w' _ _ -> BT.BaseBVRepr (addNat w w')
      BVSelect _ n _ _ -> BT.BaseBVRepr n
      BVZext w' _ _ -> BT.BaseBVRepr w'
      BVSext w' _ _ -> BT.BaseBVRepr w'
      BVShl w _ _ -> BT.BaseBVRepr w
      BVLshr w _ _ -> BT.BaseBVRepr w
      BVAshr w _ _ -> BT.BaseBVRepr w
      BVUdiv w _ _ -> BT.BaseBVRepr w
      BVUrem w _ _ -> BT.BaseBVRepr w
      BVSdiv w _ _ -> BT.BaseBVRepr w
      BVSrem w _ _ -> BT.BaseBVRepr w
      BVRol w _ _ -> BT.BaseBVRepr w
      BVRor w _ _ -> BT.BaseBVRepr w

-- | Check if expression is BVNotBits and return the inner expression
-- This is exported for use in builder/views, but implementation deferred
asBVNotBits :: Expr t f (BT.BaseBVType w) -> Maybe (Expr t f (BT.BaseBVType w))
asBVNotBits _ = Nothing  -- Will be properly implemented via views
{-# INLINE asBVNotBits #-}

width :: HasBaseType (f (Expr t f)) => Expr t f (BT.BaseBVType w) -> NatRepr w
width e = case baseType e of BT.BaseBVRepr w -> w

$(return [])

instance PC.TestEquality f => PC.TestEquality (BVExpr f) where
  testEquality =
    $(PTH.structuralTypeEquality
       [t|BVExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.testEquality|])
       , (PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType, [|PC.testEquality|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType), [|\x y -> if PBS.eqBy (\(BVExprWrapper u) (BVExprWrapper v) -> PC.isJust (PC.testEquality u v)) x y then Just PC.Refl else Nothing|])
       , (PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|\x y -> if BKv.eqBy (\u v -> PC.isJust (PC.testEquality u v)) (SR.eq (SRS.sumRepr x)) (SRS.sumMap x) (SRS.sumMap y) && SR.eq (SRS.sumRepr x) (SRS.sumOffset x) (SRS.sumOffset y) then Just PC.Refl else Nothing|])
       , (PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|\x y -> if BKv.eqBy (\u v -> PC.isJust (PC.testEquality u v)) (==) (SRP.prodMap x) (SRP.prodMap y) then Just PC.Refl else Nothing|])
       ]
     )

instance PC.OrdF f => PC.OrdF (BVExpr f) where
  compareF =
    $(PTH.structuralTypeOrd
       [t|BVExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.compareF|])
       , (PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType, [|PC.compareF|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType), [|\pbs1 pbs2 -> PC.fromOrdering (PBS.ordBy (\(BVExprWrapper u) (BVExprWrapper v) -> PC.toOrdering (PC.compareF u v)) pbs1 pbs2)|])
       , (PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|\x y -> case SR.sr_compare (SRS.sumRepr x) (SRS.sumOffset x) (SRS.sumOffset y) of { EQ -> PC.fromOrdering (BKv.ordBy (\u v -> PC.toOrdering (PC.compareF u v)) (SR.sr_compare (SRS.sumRepr x)) (SRS.sumMap x) (SRS.sumMap y)); LT -> PC.LTF; GT -> PC.GTF }|])
       , (PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|\x y -> PC.fromOrdering (BKv.ordBy (\u v -> PC.toOrdering (PC.compareF u v)) compare (SRP.prodMap x) (SRP.prodMap y))|])
       ]
     )

instance PC.HashableF f => PC.HashableF (BVExpr f) where
  hashWithSaltF =
    $(PTH.structuralHashWithSalt
       [t|BVExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.hashWithSaltF|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType), [|\s pbs -> PBS.hashPBSWith (\s' (BVExprWrapper e) -> PC.hashWithSaltF s' e) s pbs|])
       , (PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|\s ws -> let s' = foldl (\s'' (k, v) -> SR.sr_hashWithSalt (SRS.sumRepr ws) (PC.hashWithSaltF s'' k) v) s (BKv.toList (SRS.sumMap ws)) in SR.sr_hashWithSalt (SRS.sumRepr ws) s' (SRS.sumOffset ws)|])
       , (PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|\s wp -> foldl (\s' (k, v) -> PC.hashWithSaltF (hashWithSalt s' v) k) s (BKv.toList (SRP.prodMap wp))|])
       ]
     )

-- Derive instances for BVExprWrapper via StandaloneDeriving
deriving instance Eq (f (BT.BaseBVType w)) => Eq (BVExprWrapper f w)
deriving instance Show (f (BT.BaseBVType w)) => Show (BVExprWrapper f w)

-- Manual Ord instance that works when both sides have the same width
-- Used by the Template Haskell generated code
instance (Ord (f (BT.BaseBVType w)), 1 <= w) => Ord (BVExprWrapper f w) where
  compare (BVExprWrapper x) (BVExprWrapper y) = compare x y

-- Hashable instance
instance (Eq (f (BT.BaseBVType w)), PC.HashableF f, 1 <= w) => PC.Hashable (BVExprWrapper f w) where
  hashWithSalt s (BVExprWrapper expr) = PC.hashWithSaltF s expr

-- Polarizable instance
instance (EV.HasBVViews f, 1 <= w) => PBS.Polarizable (BVExprWrapper (E.Expr t f) w) where
  polarity (BVExprWrapper expr) = case EV.asBVNotBits expr of
    Just inner -> PBS.Negative (BVExprWrapper inner)
    Nothing -> PBS.Positive (BVExprWrapper expr)
  {-# INLINE polarity #-}
