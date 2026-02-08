{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

module Who2.Expr.SymExpr
  ( SymExpr(SymExpr, getSymExpr)
  ) where

import qualified Data.BitVector.Sized as BV

import qualified Data.Parameterized.Classes as PC

import qualified What4.BaseTypes as BT
import qualified What4.Utils.BVDomain as BVD
import qualified What4.Interface as WI
import qualified What4.Utils.AbstractDomains as AD

import Who2.Expr.App (App)
import Who2.Expr (Expr)
import qualified Who2.Expr as E

newtype SymExpr t tp
  = SymExpr { getSymExpr :: Expr t (App t) tp }

deriving instance AD.HasAbsValue (SymExpr t)
deriving instance E.HasBaseType (SymExpr t)
deriving instance PC.HashableF (SymExpr t)
deriving instance PC.OrdF (SymExpr t)
deriving instance PC.TestEquality (SymExpr t)

instance WI.IsExpr (SymExpr t) where
  exprType = E.baseType

  asConstantPred e = AD.getAbsValue e

  asBV e =
    case E.baseType e of
      BT.BaseBVRepr w -> BV.mkBV w <$> BVD.asSingleton (AD.getAbsValue e)

  integerBounds = error "FIXME: integerBounds"
  asFloat = error "FIXME: asFloat"
  rationalBounds = error "FIXME: rationalBounds"
  unsignedBVBounds = error "FIXME: unsignedBVBounds"
  signedBVBounds = error "FIXME: signedBVBounds"
  asAffineVar = error "FIXME: asAffineVar"
  printSymExpr = error "FIXME: printSymExpr"
  unsafeSetAbstractValue = error "FIXME: unsafeSetAbstractValue"
