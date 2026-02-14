{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Who2.ExprBuilderAPI
  ( ExprBuilderAPI(..)
  , getResultType
  ) where

import Data.Parameterized.NatRepr (NatRepr, natValue, type (<=), type (+), addNat)
import qualified Data.Parameterized.Classes as PC
import Prettyprinter (Pretty(..), parens, (<+>), viaShow)
import What4.BaseTypes
  ( BaseType
  , BaseTypeRepr(..)
  , BaseBoolType
  , BaseBVType
  )
import qualified Data.BitVector.Sized as BV

-- | GADT representing Who2 builder operations as data
-- Type parameter: result type of the expression
data ExprBuilderAPI (tp :: BaseType) where
  -- Boolean constants
  TruePred :: ExprBuilderAPI BaseBoolType
  FalsePred :: ExprBuilderAPI BaseBoolType

  -- Bound variables (identified by Int index)
  BoundVarBool :: Int -> ExprBuilderAPI BaseBoolType
  BoundVarBV :: (1 <= w) => NatRepr w -> Int -> ExprBuilderAPI (BaseBVType w)

  -- Boolean operations
  NotPred :: ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType
  AndPred :: ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType
  OrPred :: ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType
  XorPred :: ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType
  EqPred :: ExprBuilderAPI tp -> ExprBuilderAPI tp -> ExprBuilderAPI BaseBoolType
  ItePred :: ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType -> ExprBuilderAPI BaseBoolType

  -- BV literals
  BVLit :: (1 <= w) => NatRepr w -> BV.BV w -> ExprBuilderAPI (BaseBVType w)

  -- BV arithmetic
  BVAdd :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVSub :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVMul :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVNeg :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVIte :: (1 <= w) => ExprBuilderAPI BaseBoolType -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)

  -- BV bitwise
  BVAndBits :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVOrBits :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVXorBits :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVNotBits :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)

  -- BV comparisons
  BVUlt :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI BaseBoolType
  BVSlt :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI BaseBoolType
  BVEq :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI BaseBoolType

  -- BV shifts
  BVShl :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVLshr :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVAshr :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)

  -- BV division/remainder
  BVUdiv :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVUrem :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVSdiv :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVSrem :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)

  -- BV rotation
  BVRol :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)
  BVRor :: (1 <= w) => ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType w)

  -- BV manipulation
  BVConcat :: (1 <= u, 1 <= v, 1 <= (u + v)) => ExprBuilderAPI (BaseBVType u) -> ExprBuilderAPI (BaseBVType v) -> ExprBuilderAPI (BaseBVType (u + v))
  BVSelect :: (1 <= w, 1 <= idx, (idx + w) <= n) => NatRepr idx -> NatRepr w -> ExprBuilderAPI (BaseBVType n) -> ExprBuilderAPI (BaseBVType w)
  BVZext :: (1 <= w, (w + 1) <= r, 1 <= r) => NatRepr r -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType r)
  BVSext :: (1 <= w, (w + 1) <= r, 1 <= r) => NatRepr r -> ExprBuilderAPI (BaseBVType w) -> ExprBuilderAPI (BaseBVType r)

-- | Get the result type of an expression
getResultType :: ExprBuilderAPI tp -> BaseTypeRepr tp
getResultType = \case
  TruePred -> BaseBoolRepr
  FalsePred -> BaseBoolRepr
  BoundVarBool _ -> BaseBoolRepr
  BoundVarBV w _ -> BaseBVRepr w
  NotPred _ -> BaseBoolRepr
  AndPred _ _ -> BaseBoolRepr
  OrPred _ _ -> BaseBoolRepr
  XorPred _ _ -> BaseBoolRepr
  EqPred _ _ -> BaseBoolRepr
  ItePred _ _ _ -> BaseBoolRepr
  BVLit w _ -> BaseBVRepr w
  BVAdd x _ -> getResultType x
  BVSub x _ -> getResultType x
  BVMul x _ -> getResultType x
  BVNeg x -> getResultType x
  BVIte _ t _ -> getResultType t
  BVAndBits x _ -> getResultType x
  BVOrBits x _ -> getResultType x
  BVXorBits x _ -> getResultType x
  BVNotBits x -> getResultType x
  BVUlt _ _ -> BaseBoolRepr
  BVSlt _ _ -> BaseBoolRepr
  BVEq _ _ -> BaseBoolRepr
  BVShl x _ -> getResultType x
  BVLshr x _ -> getResultType x
  BVAshr x _ -> getResultType x
  BVUdiv x _ -> getResultType x
  BVUrem x _ -> getResultType x
  BVSdiv x _ -> getResultType x
  BVSrem x _ -> getResultType x
  BVRol x _ -> getResultType x
  BVRor x _ -> getResultType x
  BVConcat x y ->
    case (getResultType x, getResultType y) of
      (BaseBVRepr u, BaseBVRepr v) -> BaseBVRepr (addNat u v)
  BVSelect _ w _ -> BaseBVRepr w
  BVZext r _ -> BaseBVRepr r
  BVSext r _ -> BaseBVRepr r

-- | Pretty instance for expression rendering
instance Pretty (ExprBuilderAPI tp) where
  pretty = \case
    TruePred -> pretty @String "true"
    FalsePred -> pretty @String "false"
    BoundVarBool i -> pretty @String "bool_" <> viaShow i
    BoundVarBV w i -> pretty @String "bv" <> viaShow (natValue w) <> pretty @String "_" <> viaShow i
    NotPred x -> parens $ pretty @String "not" <+> pretty x
    AndPred x y -> parens $ pretty @String "and" <+> pretty x <+> pretty y
    OrPred x y -> parens $ pretty @String "or" <+> pretty x <+> pretty y
    XorPred x y -> parens $ pretty @String "xor" <+> pretty x <+> pretty y
    EqPred x y -> parens $ pretty @String "=" <+> pretty x <+> pretty y
    ItePred c t e -> parens $ pretty @String "ite" <+> pretty c <+> pretty t <+> pretty e
    BVLit w bv -> pretty @String "#x" <> viaShow bv <> pretty @String ":" <> viaShow (natValue w)
    BVAdd x y -> parens $ pretty @String "bvadd" <+> pretty x <+> pretty y
    BVSub x y -> parens $ pretty @String "bvsub" <+> pretty x <+> pretty y
    BVMul x y -> parens $ pretty @String "bvmul" <+> pretty x <+> pretty y
    BVNeg x -> parens $ pretty @String "bvneg" <+> pretty x
    BVIte c t e -> parens $ pretty @String "ite" <+> pretty c <+> pretty t <+> pretty e
    BVAndBits x y -> parens $ pretty @String "bvand" <+> pretty x <+> pretty y
    BVOrBits x y -> parens $ pretty @String "bvor" <+> pretty x <+> pretty y
    BVXorBits x y -> parens $ pretty @String "bvxor" <+> pretty x <+> pretty y
    BVNotBits x -> parens $ pretty @String "bvnot" <+> pretty x
    BVUlt x y -> parens $ pretty @String "bvult" <+> pretty x <+> pretty y
    BVSlt x y -> parens $ pretty @String "bvslt" <+> pretty x <+> pretty y
    BVEq x y -> parens $ pretty @String "=" <+> pretty x <+> pretty y
    BVShl x y -> parens $ pretty @String "bvshl" <+> pretty x <+> pretty y
    BVLshr x y -> parens $ pretty @String "bvlshr" <+> pretty x <+> pretty y
    BVAshr x y -> parens $ pretty @String "bvashr" <+> pretty x <+> pretty y
    BVUdiv x y -> parens $ pretty @String "bvudiv" <+> pretty x <+> pretty y
    BVUrem x y -> parens $ pretty @String "bvurem" <+> pretty x <+> pretty y
    BVSdiv x y -> parens $ pretty @String "bvsdiv" <+> pretty x <+> pretty y
    BVSrem x y -> parens $ pretty @String "bvsrem" <+> pretty x <+> pretty y
    BVRol x y -> parens $ pretty @String "bvrol" <+> pretty x <+> pretty y
    BVRor x y -> parens $ pretty @String "bvror" <+> pretty x <+> pretty y
    BVConcat x y -> parens $ pretty @String "concat" <+> pretty x <+> pretty y
    BVSelect idx w x -> parens $ pretty @String "select" <+> viaShow (natValue idx) <+> viaShow (natValue w) <+> pretty x
    BVZext r x -> parens $ pretty @String "zext" <+> viaShow (natValue r) <+> pretty x
    BVSext r x -> parens $ pretty @String "sext" <+> viaShow (natValue r) <+> pretty x

-- Show instance via Pretty
instance Show (ExprBuilderAPI tp) where
  show = show . pretty

-- ShowF instance for Hedgehog's forAll
instance PC.ShowF ExprBuilderAPI where
  showF = show
