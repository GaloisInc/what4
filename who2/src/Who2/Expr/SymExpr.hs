{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module Who2.Expr.SymExpr
  ( SymExpr(SymExpr, getSymExpr)
  ) where

import qualified Data.BitVector.Sized as BV
import qualified Prettyprinter as PP

import qualified Data.Parameterized.Classes as PC

import qualified What4.BaseTypes as BT
import qualified What4.Utils.BVDomain as BVD
import qualified What4.Interface as WI
import qualified What4.Utils.AbstractDomains as AD

import Who2.Expr.App (App)
import Who2.Expr (Expr)
import qualified Who2.Expr as E
import qualified Who2.Expr.App as App

newtype SymExpr t tp
  = SymExpr { getSymExpr :: Expr t (App t) tp }

deriving instance AD.HasAbsValue (SymExpr t)
deriving instance E.HasBaseType (SymExpr t)
deriving instance PC.HashableF (SymExpr t)
deriving instance PC.OrdF (SymExpr t)
deriving instance PC.TestEquality (SymExpr t)

instance PP.Pretty (SymExpr t tp) where
  pretty = ppSymExpr
    where
      ppSymExpr :: forall ann tp'. SymExpr t tp' -> PP.Doc ann
      ppSymExpr (SymExpr e) = E.pretty ppApp e

      ppApp :: forall ann tp'. App t (Expr t (App t)) tp' -> PP.Doc ann
      ppApp = App.pretty (ppSymExpr . SymExpr)

instance WI.IsExpr (SymExpr t) where
  exprType = E.baseType

  asConstantPred e = AD.getAbsValue e

  asBV e =
    case E.baseType e of
      BT.BaseBVRepr w -> BV.mkBV w <$> BVD.asSingleton (AD.getAbsValue e)

  integerBounds = error "Who2.Expr.SymExpr.integerBounds: not yet supported in Who2"

  asFloat = error "Who2.Expr.SymExpr.asFloat: not yet supported in Who2"

  rationalBounds = error "Who2.Expr.SymExpr.rationalBounds: not yet supported in Who2"

  unsignedBVBounds e =
    case E.baseType e of
      BT.BaseBVRepr _ -> Just $ BVD.ubounds (AD.getAbsValue e)

  signedBVBounds e =
    case E.baseType e of
      BT.BaseBVRepr w -> Just $ BVD.sbounds w (AD.getAbsValue e)

  asAffineVar = error "Who2.Expr.SymExpr.asAffineVar: not yet supported in Who2"

  printSymExpr = PP.pretty

  unsafeSetAbstractValue av (SymExpr e) =
    SymExpr $ e { E.eAbsVal = av }
