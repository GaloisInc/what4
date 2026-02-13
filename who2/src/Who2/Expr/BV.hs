{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
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
  , pretty
  ) where

import Data.Kind (Type)
import Data.Hashable (hashWithSalt)
import Data.Type.Equality (type (:~:)(..))

import qualified Data.BitVector.Sized as BV
import qualified Prettyprinter as PP

import qualified Data.Parameterized.Classes as PC
import           Data.Parameterized.NatRepr (type (<=), type (+), NatRepr, addNat)
import qualified Data.Parameterized.TH.GADT as PTH

import qualified What4.BaseTypes as BT

import qualified What4.SemiRing as SR

import Who2.Expr (Expr, HasBaseType(baseType))
import qualified Who2.Expr as E
import qualified Who2.Expr.Bloom.Kv as BKv
import qualified Who2.Expr.Bloom.Polarized as PBS
import qualified Who2.Expr.Views as EV
import qualified Who2.Expr.SemiRing.Product as SRP
import qualified Who2.Expr.SemiRing.Sum as SRS
import qualified Who2.Expr.HashConsed.PolarizedExprSet as PES
import qualified Who2.Expr.HashConsed.SRSum as HCSR
import qualified Who2.Expr.HashConsed.SRProd as HCPR

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

  -- Hash-consed BV bitwise operations using PolarizedExprSet
  BVAndBitsHC ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(PES.PolarizedExprSet f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  BVOrBitsHC ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(PES.PolarizedExprSet f (BT.BaseBVType w)) ->
    BVExpr f (BT.BaseBVType w)

  -- Hash-consed BV arithmetic using SRSum/SRProd
  BVAddHC ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(HCSR.SRSum (SR.SemiRingBV SR.BVArith w) f) ->
    BVExpr f (BT.BaseBVType w)

  BVMulHC ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(HCPR.SRProd (SR.SemiRingBV SR.BVBits w) f) ->
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
      BVAndBitsHC w _ -> BT.BaseBVRepr w
      BVOrBitsHC w _ -> BT.BaseBVRepr w
      BVAddHC w _ -> BT.BaseBVRepr w
      BVMulHC w _ -> BT.BaseBVRepr w

-- | Check if expression is BVNotBits and return the inner expression
-- This is exported for use in builder/views, but implementation deferred
asBVNotBits :: Expr t f (BT.BaseBVType w) -> Maybe (Expr t f (BT.BaseBVType w))
asBVNotBits _ = Nothing  -- Will be properly implemented via views
{-# INLINE asBVNotBits #-}

width :: HasBaseType (f (Expr t f)) => Expr t f (BT.BaseBVType w) -> NatRepr w
width e = case baseType e of BT.BaseBVRepr w -> w

------------------------------------------------------------------------
-- Helper functions for Template Haskell instances

-- TestEquality helpers

testEqPolarizedBloomSeq ::
  PC.TestEquality f =>
  PBS.PolarizedBloomSeq (BVExprWrapper f w) ->
  PBS.PolarizedBloomSeq (BVExprWrapper f w) ->
  Maybe (w :~: w)
testEqPolarizedBloomSeq x y =
  if PBS.eqBy (\(BVExprWrapper u) (BVExprWrapper v) -> PC.isJust (PC.testEquality u v)) x y
  then Just PC.Refl
  else Nothing
{-# INLINE testEqPolarizedBloomSeq #-}

testEqSRSum ::
  PC.TestEquality f =>
  SRS.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  SRS.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  Maybe (w :~: w)
testEqSRSum x y =
  if BKv.eqBy (\u v -> PC.isJust (PC.testEquality u v)) (SR.eq (SRS.sumRepr x)) (SRS.sumMap x) (SRS.sumMap y)
     && SR.eq (SRS.sumRepr x) (SRS.sumOffset x) (SRS.sumOffset y)
  then Just PC.Refl
  else Nothing
{-# INLINE testEqSRSum #-}

testEqSRProd ::
  PC.TestEquality f =>
  SRP.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  SRP.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  Maybe (w :~: w)
testEqSRProd x y =
  if BKv.eqBy (\u v -> PC.isJust (PC.testEquality u v)) (==) (SRP.prodMap x) (SRP.prodMap y)
  then Just PC.Refl
  else Nothing
{-# INLINE testEqSRProd #-}

testEqPolarizedExprSet ::
  PC.TestEquality f =>
  PES.PolarizedExprSet f (BT.BaseBVType w) ->
  PES.PolarizedExprSet f (BT.BaseBVType w) ->
  Maybe (w :~: w)
testEqPolarizedExprSet x y =
  if PES.eqBy (\u v -> PC.isJust (PC.testEquality u v)) x y
  then Just PC.Refl
  else Nothing
{-# INLINE testEqPolarizedExprSet #-}

testEqHCSRSum ::
  PC.TestEquality f =>
  HCSR.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  HCSR.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  Maybe (w :~: w)
testEqHCSRSum x y =
  if SR.eq (HCSR.sumRepr x) (HCSR.sumOffset x) (HCSR.sumOffset y)
     && all (\((k1,v1),(k2,v2)) -> PC.isJust (PC.testEquality k1 k2) && SR.eq (HCSR.sumRepr x) v1 v2)
            (zip (HCSR.toTerms x) (HCSR.toTerms y))
  then Just PC.Refl
  else Nothing
{-# INLINE testEqHCSRSum #-}

testEqHCSRProd ::
  PC.TestEquality f =>
  HCPR.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  HCPR.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  Maybe (w :~: w)
testEqHCSRProd x y =
  if HCPR.prodCoeff x == HCPR.prodCoeff y
     && all (\((k1,v1),(k2,v2)) -> PC.isJust (PC.testEquality k1 k2) && v1 == v2)
            (zip (HCPR.toTerms x) (HCPR.toTerms y))
  then Just PC.Refl
  else Nothing
{-# INLINE testEqHCSRProd #-}

-- OrdF helpers

comparePolarizedBloomSeq ::
  PC.OrdF f =>
  PBS.PolarizedBloomSeq (BVExprWrapper f w) ->
  PBS.PolarizedBloomSeq (BVExprWrapper f w) ->
  PC.OrderingF w w
comparePolarizedBloomSeq pbs1 pbs2 =
  PC.fromOrdering (PBS.ordBy (\(BVExprWrapper u) (BVExprWrapper v) -> PC.toOrdering (PC.compareF u v)) pbs1 pbs2)
{-# INLINE comparePolarizedBloomSeq #-}

compareSRSum ::
  PC.OrdF f =>
  SRS.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  SRS.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  PC.OrderingF w w
compareSRSum x y =
  case SR.sr_compare (SRS.sumRepr x) (SRS.sumOffset x) (SRS.sumOffset y) of
    EQ -> PC.fromOrdering (BKv.ordBy (\u v -> PC.toOrdering (PC.compareF u v))
                                     (SR.sr_compare (SRS.sumRepr x))
                                     (SRS.sumMap x)
                                     (SRS.sumMap y))
    LT -> PC.LTF
    GT -> PC.GTF
{-# INLINE compareSRSum #-}

compareSRProd ::
  PC.OrdF f =>
  SRP.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  SRP.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  PC.OrderingF w w
compareSRProd x y =
  PC.fromOrdering (BKv.ordBy (\u v -> PC.toOrdering (PC.compareF u v)) compare (SRP.prodMap x) (SRP.prodMap y))
{-# INLINE compareSRProd #-}

comparePolarizedExprSet ::
  PC.OrdF f =>
  PES.PolarizedExprSet f (BT.BaseBVType w) ->
  PES.PolarizedExprSet f (BT.BaseBVType w) ->
  PC.OrderingF w w
comparePolarizedExprSet pset1 pset2 =
  PC.fromOrdering (PES.ordBy (\u v -> PC.toOrdering (PC.compareF u v)) pset1 pset2)
{-# INLINE comparePolarizedExprSet #-}

compareHCSRSum ::
  PC.OrdF f =>
  HCSR.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  HCSR.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  PC.OrderingF w w
compareHCSRSum x y =
  let ordByTerms _ [] [] = EQ
      ordByTerms _ [] _  = LT
      ordByTerms _ _  [] = GT
      ordByTerms f (a:as) (b:bs) =
        case f a b of
          LT -> LT
          GT -> GT
          EQ -> ordByTerms f as bs
  in case SR.sr_compare (HCSR.sumRepr x) (HCSR.sumOffset x) (HCSR.sumOffset y) of
       EQ -> PC.fromOrdering (ordByTerms (\(k1,v1) (k2,v2) ->
                                            case PC.toOrdering (PC.compareF k1 k2) of
                                              LT -> LT
                                              GT -> GT
                                              EQ -> SR.sr_compare (HCSR.sumRepr x) v1 v2)
                                         (HCSR.toTerms x)
                                         (HCSR.toTerms y))
       LT -> PC.LTF
       GT -> PC.GTF
{-# INLINE compareHCSRSum #-}

compareHCSRProd ::
  PC.OrdF f =>
  HCPR.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  HCPR.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  PC.OrderingF w w
compareHCSRProd x y =
  let ordByTerms _ [] [] = EQ
      ordByTerms _ [] _  = LT
      ordByTerms _ _  [] = GT
      ordByTerms f (a:as) (b:bs) =
        case f a b of
          LT -> LT
          GT -> GT
          EQ -> ordByTerms f as bs
  in PC.fromOrdering (ordByTerms (\(k1,v1) (k2,v2) ->
                                    case PC.toOrdering (PC.compareF k1 k2) of
                                      LT -> LT
                                      GT -> GT
                                      EQ -> compare v1 v2)
                                 (HCPR.toTerms x)
                                 (HCPR.toTerms y))
{-# INLINE compareHCSRProd #-}

-- HashableF helpers

hashPolarizedBloomSeq ::
  PC.HashableF f =>
  Int ->
  PBS.PolarizedBloomSeq (BVExprWrapper f w) ->
  Int
hashPolarizedBloomSeq s pbs =
  PBS.hashPBSWith (\s' (BVExprWrapper e) -> PC.hashWithSaltF s' e) s pbs
{-# INLINE hashPolarizedBloomSeq #-}

hashSRSum ::
  PC.HashableF f =>
  Int ->
  SRS.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  Int
hashSRSum s ws =
  let s' = foldl (\s'' (k, v) -> SR.sr_hashWithSalt (SRS.sumRepr ws) (PC.hashWithSaltF s'' k) v)
                s
                (BKv.toList (SRS.sumMap ws))
  in SR.sr_hashWithSalt (SRS.sumRepr ws) s' (SRS.sumOffset ws)
{-# INLINE hashSRSum #-}

hashSRProd ::
  PC.HashableF f =>
  Int ->
  SRP.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  Int
hashSRProd s wp =
  foldl (\s' (k, v) -> PC.hashWithSaltF (hashWithSalt s' v) k) s (BKv.toList (SRP.prodMap wp))
{-# INLINE hashSRProd #-}

hashPolarizedExprSet ::
  PC.HashableF f =>
  Int ->
  PES.PolarizedExprSet f (BT.BaseBVType w) ->
  Int
hashPolarizedExprSet s pset =
  PES.hashPESWith (\s' e -> PC.hashWithSaltF s' e) s pset
{-# INLINE hashPolarizedExprSet #-}

hashHCSRSum ::
  PC.HashableF f =>
  Int ->
  HCSR.SRSum (SR.SemiRingBV SR.BVArith w) f ->
  Int
hashHCSRSum s ws =
  let s' = foldl (\s'' (k, v) -> SR.sr_hashWithSalt (HCSR.sumRepr ws) (PC.hashWithSaltF s'' k) v)
                s
                (HCSR.toTerms ws)
  in SR.sr_hashWithSalt (HCSR.sumRepr ws) s' (HCSR.sumOffset ws)
{-# INLINE hashHCSRSum #-}

hashHCSRProd ::
  PC.HashableF f =>
  Int ->
  HCPR.SRProd (SR.SemiRingBV SR.BVBits w) f ->
  Int
hashHCSRProd s wp =
  foldl (\s' (k, v) -> PC.hashWithSaltF (hashWithSalt s' v) k) s (HCPR.toTerms wp)
{-# INLINE hashHCSRProd #-}

$(return [])

instance PC.TestEquality f => PC.TestEquality (BVExpr f) where
  testEquality =
    $(PTH.structuralTypeEquality
       [t|BVExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.testEquality|])
       , (PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType, [|PC.testEquality|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType), [|testEqPolarizedBloomSeq|])
       , (PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|testEqSRSum|])
       , (PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|testEqSRProd|])
       , (PTH.ConType [t|PES.PolarizedExprSet|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|testEqPolarizedExprSet|])
       , (PTH.ConType [t|HCSR.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|testEqHCSRSum|])
       , (PTH.ConType [t|HCPR.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|testEqHCSRProd|])
       ]
     )

instance PC.OrdF f => PC.OrdF (BVExpr f) where
  compareF =
    $(PTH.structuralTypeOrd
       [t|BVExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.compareF|])
       , (PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType, [|PC.compareF|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType), [|comparePolarizedBloomSeq|])
       , (PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|compareSRSum|])
       , (PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|compareSRProd|])
       , (PTH.ConType [t|PES.PolarizedExprSet|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|comparePolarizedExprSet|])
       , (PTH.ConType [t|HCSR.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|compareHCSRSum|])
       , (PTH.ConType [t|HCPR.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|compareHCSRProd|])
       ]
     )

instance PC.HashableF f => PC.HashableF (BVExpr f) where
  hashWithSaltF =
    $(PTH.structuralHashWithSalt
       [t|BVExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.hashWithSaltF|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType), [|hashPolarizedBloomSeq|])
       , (PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|hashSRSum|])
       , (PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|hashSRProd|])
       , (PTH.ConType [t|PES.PolarizedExprSet|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|hashPolarizedExprSet|])
       , (PTH.ConType [t|HCSR.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|hashHCSRSum|])
       , (PTH.ConType [t|HCPR.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|hashHCSRProd|])
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

-- Polarizable instance for BVExprWrapper
instance (EV.HasBVViews f, 1 <= w) => PBS.Polarizable (BVExprWrapper (E.Expr t f) w) where
  polarity (BVExprWrapper expr) = case EV.asBVNotBits expr of
    Just inner -> PBS.Negative (BVExprWrapper inner)
    Nothing -> PBS.Positive (BVExprWrapper expr)
  {-# INLINE polarity #-}

-- Polarizable instance for Expr for hash-consed PolarizedExprSet
instance (EV.HasBVViews f, 1 <= w) => PBS.Polarizable (E.Expr t f (BT.BaseBVType w)) where
  polarity expr = case EV.asBVNotBits expr of
    Just inner -> PBS.Negative inner
    Nothing -> PBS.Positive expr
  {-# INLINE polarity #-}

-- | Pretty-print a bitvector expression given a pretty-printer for the term functor
pretty :: (forall tp'. f tp' -> PP.Doc ann) -> BVExpr f tp -> PP.Doc ann
pretty ppF = \case
  BVLit _w bv -> PP.pretty "#x" PP.<> PP.pretty (show bv)
  BVAdd _w _ws -> PP.pretty "bv_add"
  BVNeg _w x -> PP.parens $ PP.pretty "bvneg" PP.<+> ppF x
  BVSub _w x y -> PP.parens $ PP.pretty "bvsub" PP.<+> ppF x PP.<+> ppF y
  BVMul _w _wp -> PP.pretty "bv_mul"
  BVAndBits _w _pbs -> PP.pretty "bvand"
  BVOrBits _w _pbs -> PP.pretty "bvor"
  BVXorBits _w x y -> PP.parens $ PP.pretty "bvxor" PP.<+> ppF x PP.<+> ppF y
  BVNotBits _w x -> PP.parens $ PP.pretty "bvnot" PP.<+> ppF x
  BVConcat _w _w' x y -> PP.parens $ PP.pretty "concat" PP.<+> ppF x PP.<+> ppF y
  BVSelect _i _n _w x -> PP.parens $ PP.pretty "select" PP.<+> ppF x
  BVZext _w' _w x -> PP.parens $ PP.pretty "zero_extend" PP.<+> ppF x
  BVSext _w' _w x -> PP.parens $ PP.pretty "sign_extend" PP.<+> ppF x
  BVShl _w x y -> PP.parens $ PP.pretty "bvshl" PP.<+> ppF x PP.<+> ppF y
  BVLshr _w x y -> PP.parens $ PP.pretty "bvlshr" PP.<+> ppF x PP.<+> ppF y
  BVAshr _w x y -> PP.parens $ PP.pretty "bvashr" PP.<+> ppF x PP.<+> ppF y
  BVUdiv _w x y -> PP.parens $ PP.pretty "bvudiv" PP.<+> ppF x PP.<+> ppF y
  BVUrem _w x y -> PP.parens $ PP.pretty "bvurem" PP.<+> ppF x PP.<+> ppF y
  BVSdiv _w x y -> PP.parens $ PP.pretty "bvsdiv" PP.<+> ppF x PP.<+> ppF y
  BVSrem _w x y -> PP.parens $ PP.pretty "bvsrem" PP.<+> ppF x PP.<+> ppF y
  BVRol _w x y -> PP.parens $ PP.pretty "rotate_left" PP.<+> ppF x PP.<+> ppF y
  BVRor _w x y -> PP.parens $ PP.pretty "rotate_right" PP.<+> ppF x PP.<+> ppF y
  BVAndBitsHC _w _ -> PP.pretty "bvand_hc"
  BVOrBitsHC _w _ -> PP.pretty "bvor_hc"
  BVAddHC _w _ -> PP.pretty "bv_add_hc"
  BVMulHC _w _ -> PP.pretty "bv_mul_hc"
