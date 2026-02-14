{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
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
import Data.Type.Equality (type (:~:)(Refl))

import qualified Data.BitVector.Sized as BV
import qualified Prettyprinter as PP

import qualified Data.Parameterized.Classes as PC
import           Data.Parameterized.NatRepr (type (<=), type (+), NatRepr, addNat)
import qualified Data.Parameterized.TH.GADT as PTH

import qualified What4.BaseTypes as BT

import qualified What4.SemiRing as SR

import Who2.Expr (Expr, HasBaseType(baseType))
import qualified Who2.Expr as E
import qualified Who2.Expr.Bloom.Polarized as PBS
import qualified Who2.Expr.Views as EV
import qualified Who2.Expr.Bloom.SemiRing.Product as SRP
import qualified Who2.Expr.Bloom.SemiRing.Sum as SRS
import qualified Who2.Expr.HashConsed.Polarized as PES
import qualified Who2.Expr.HashConsed.SemiRing.Sum as HCSR
import qualified Who2.Expr.HashConsed.SemiRing.Product as HCPR

-- | 'Polarizable' wrapper for bitvector expressions
--
-- Used in both 'BVAndBits' and 'BVOrBits'.
newtype BVExprWrapper f w = BVExprWrapper { unBVExprWrapper :: f (BT.BaseBVType w) }

instance PC.TestEquality f => PC.TestEquality (BVExprWrapper f) where
  testEquality (BVExprWrapper x) (BVExprWrapper y) =
    case PC.testEquality x y of
      Nothing -> Nothing
      Just Refl -> Just Refl

instance PC.OrdF f => PC.OrdF (BVExprWrapper f) where
  compareF (BVExprWrapper x) (BVExprWrapper y) =
    case PC.compareF x y of
      PC.LTF -> PC.LTF
      PC.GTF -> PC.GTF
      PC.EQF -> PC.EQF

deriving instance Show (f (BT.BaseBVType w)) => Show (BVExprWrapper f w)

instance PC.TestEquality f => Eq (BVExprWrapper f w) where
  x == y = PC.isJust (PC.testEquality x y)

-- -- Manual Ord instance that works when both sides have the same width
-- -- Used by the Template Haskell generated code
-- instance (Ord (f (BT.BaseBVType w)), 1 <= w) => Ord (BVExprWrapper f w) where
--   compare (BVExprWrapper x) (BVExprWrapper y) = compare x y

-- -- Hashable instance
instance (BT.TestEquality f, PC.HashableF f, 1 <= w) => PC.Hashable (BVExprWrapper f w) where
  hashWithSalt s (BVExprWrapper expr) = PC.hashWithSaltF s expr

-- Polarizable instance for BVExprWrapper
instance (EV.HasBVViews f, 1 <= w) => PBS.Polarizable (BVExprWrapper (E.Expr t f) w) where
  polarity (BVExprWrapper expr) = case EV.asBVNotBits expr of
    Just inner -> PBS.Negative (BVExprWrapper inner)
    Nothing -> PBS.Positive (BVExprWrapper expr)
  {-# INLINE polarity #-}

-- TODO: Why necessary?
-- Polarizable instance for Expr for hash-consed PolarizedExprSet
instance (EV.HasBVViews f, 1 <= w) => PBS.Polarizable (E.Expr t f (BT.BaseBVType w)) where
  polarity expr = case EV.asBVNotBits expr of
    Just inner -> PBS.Negative inner
    Nothing -> PBS.Positive expr
  {-# INLINE polarity #-}

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
    !(PES.PolarizedExprSet (f (BT.BaseBVType w))) ->
    BVExpr f (BT.BaseBVType w)

  BVOrBitsHC ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(PES.PolarizedExprSet (f (BT.BaseBVType w))) ->
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

testEq :: PC.TestEquality f => f x -> f y -> Bool
testEq x y = PC.isJust (PC.testEquality x y)
{-# INLINE testEq #-}

viaEq ::
  Eq a =>
  a ->
  a ->
  Maybe (b :~: b)
viaEq x y = if x == y then Just Refl else Nothing
{-# INLINE viaEq #-}

viaEqBy ::
  PC.TestEquality f =>
  ((f x -> f x -> Bool) -> g f -> g f -> Bool) ->
  g f ->
  g f ->
  Maybe (b :~: b)
viaEqBy eqBy x y = if eqBy testEq x y then Just Refl else Nothing
{-# INLINE viaEqBy #-}

viaOrd ::
  Ord a =>
  a ->
  a ->
  PC.OrderingF b b
viaOrd x y = PC.fromOrdering (compare x y)
{-# INLINE viaOrd #-}

viaOrdBy ::
  PC.OrdF f =>
  ((f x -> f y -> Ordering) -> a -> b -> Ordering) ->
  a ->
  b ->
  PC.OrderingF c c
viaOrdBy cmp x y =
  PC.fromOrdering (cmp (\u v -> PC.toOrdering (PC.compareF u v)) x y)
{-# INLINE viaOrdBy #-}

$(return [])

instance PC.TestEquality f => PC.TestEquality (BVExpr f) where
  testEquality =
    $(PTH.structuralTypeEquality
       [t|BVExpr|]
       [ ( PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType
         , [|PC.testEquality|]
         )
       , ( PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType
         , [|PC.testEquality|]
         )
       , ( PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType)
         , [|viaEq|]
         )
       , ( PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaEqBy SRS.eqBy|]
         )
       , ( PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaEqBy SRP.eqBy|]
         )
       , ( PTH.ConType [t|PES.PolarizedExprSet|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaEq|]
         )
       , ( PTH.ConType [t|HCSR.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaEqBy HCSR.eqBy|]
         )
       , ( PTH.ConType [t|HCPR.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaEqBy HCPR.eqBy|]
         )
       ]
     )

instance PC.OrdF f => PC.OrdF (BVExpr f) where
  compareF =
    $(PTH.structuralTypeOrd
       [t|BVExpr|]
       [ ( PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType
         , [|PC.compareF|]
         )
       , ( PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType
         , [|PC.compareF|]
         )
       , ( PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType)
         , [|viaOrdBy PBS.ordBy|]
         )
       , ( PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaOrdBy SRS.ordBy|]
         )
       , ( PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaOrdBy SRP.ordBy|]
         )
       , ( PTH.ConType [t|PES.PolarizedExprSet|] `PTH.TypeApp` PTH.AnyType
         , [|viaOrd|]
         )
       , ( PTH.ConType [t|HCSR.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaOrdBy HCSR.ordBy|]
         )
       , ( PTH.ConType [t|HCPR.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|viaOrdBy HCPR.ordBy|]
         )
       ]
     )

instance
  ( PC.HashableF f
  , PC.TestEquality f
  , forall w. (1 <= w) => PC.Hashable (f (BT.BaseBVType w))
  ) => PC.HashableF (BVExpr f) where
  hashWithSaltF =
    $(PTH.structuralHashWithSalt
       [t|BVExpr|]
       [ ( PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType
         , [|PC.hashWithSaltF|]
         )
       , ( PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BVExprWrapper|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType)
         , [|hashWithSalt|]
         )
       , ( PTH.ConType [t|SRS.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|hashWithSalt|]
         )
       , ( PTH.ConType [t|SRP.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|hashWithSalt|]
         )
       , ( PTH.ConType [t|PES.PolarizedExprSet|] `PTH.TypeApp` PTH.AnyType
         , [|hashWithSalt|]
         )
       , ( PTH.ConType [t|HCSR.SRSum|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|hashWithSalt|]
         )
       , ( PTH.ConType [t|HCPR.SRProd|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType
         , [|hashWithSalt|]
         )
       ]
     )

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
