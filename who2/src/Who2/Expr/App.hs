{-|
Module      : Who2.Expr.App
Copyright   : (c) Galois Inc, 2026
License     : BSD3
Maintainer  : langston@galois.com

This module defines datastructures that encode the syntax of expressions used in
"Who2.Builder".

Like "What4.Expr.App", this module uses normalizing datastructures. Unlike
those in What4, the ones used here are roughly constant-time, leading to roughly
linear time expression construction.
-}


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Who2.Expr.App
  ( App(..)
  , pretty
  ) where

import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Type.Equality (TestEquality(testEquality))

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.TH.GADT as PTH
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Prettyprinter as PP

import qualified What4.BaseTypes as BT
import qualified What4.Expr as WE
import qualified What4.Expr.App as WEA

import qualified Who2.Expr as E
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.SymFn as ESF
import qualified Who2.Expr.Views as EV

-- | Expression datatype, used as the @f@ parameter to 'Who2.Expr.Expr'.
data App t (f :: BT.BaseType -> Type) (tp :: BT.BaseType) where
  BoundVarApp :: WE.ExprBoundVar t tp -> App t f tp
  BVApp :: EBV.BVExpr f tp -> App t f tp
  LogicApp :: EL.LogicExpr f tp -> App t f tp
  FnApp :: ESF.SymFn t f args ret -> Ctx.Assignment f args -> App t f ret

instance (PC.HashableF f, TestEquality f, PC.Hashable (f BT.BaseBoolType)) => PC.HashableF (App t f) where
  hashWithSaltF salt =
    \case
      BoundVarApp x -> PC.hashWithSaltF salt x
      BVApp x -> PC.hashWithSaltF salt x
      LogicApp x -> PC.hashWithSaltF salt x
      FnApp fn args -> PC.hashWithSaltF (ESF.hashSymFn salt fn) args

instance (TestEquality f, E.HasBaseType f) => E.HasBaseType (App t f) where
  baseType =
    \case
      BoundVarApp v -> WEA.bvarType v
      BVApp bv -> E.baseType bv
      LogicApp l -> E.baseType l
      FnApp fn _ -> ESF.symFnReturnType fn

instance EV.HasLogicViews (App t) where
  asNotPred e = case E.eApp e of
    LogicApp (EL.NotPred inner) -> Just inner
    _ -> Nothing

  asAndPred e = case E.eApp e of
    LogicApp (EL.AndPred pbs) -> Just (coerce pbs)
    _ -> Nothing

  asOrPred e = case E.eApp e of
    LogicApp (EL.OrPred pbs) -> Just (coerce pbs)
    _ -> Nothing

  asIte e = case E.eApp e of
    LogicApp (EL.Ite c t f) -> Just (c, t, f)
    _ -> Nothing

instance EV.HasBVViews (App t) where
  asBVLit e = case E.eApp e of
    BVApp (EBV.BVLit w bv) -> Just (w, bv)
    _ -> Nothing

  asBVNotBits e = case E.eApp e of
    BVApp (EBV.BVNotBits _ inner) -> Just inner
    _ -> Nothing

  asBVNeg e = case E.eApp e of
    BVApp (EBV.BVNeg _ inner) -> Just inner
    _ -> Nothing

  asBVAdd e = case E.eApp e of
    BVApp (EBV.BVAdd _ ws) -> Just ws
    _ -> Nothing

  asBVMul e = case E.eApp e of
    BVApp (EBV.BVMul _ wp) -> Just wp
    _ -> Nothing

  asBVAndBits e = case E.eApp e of
    BVApp (EBV.BVAndBits _ pbs) -> Just (coerce pbs)
    _ -> Nothing

  asBVOrBits e = case E.eApp e of
    BVApp (EBV.BVOrBits _ pbs) -> Just (coerce pbs)
    _ -> Nothing

instance TestEquality f => TestEquality (App t f) where
  testEquality x y =
    case (x, y) of
      (BoundVarApp a, BoundVarApp b) -> testEquality a b
      (BoundVarApp {}, _) -> Nothing

      (BVApp a, BVApp b) -> testEquality a b
      (BVApp {}, _) -> Nothing

      (LogicApp a, LogicApp b) -> testEquality a b
      (LogicApp {}, _) -> Nothing

      (FnApp fn1 args1, FnApp fn2 args2) ->
        case ESF.testSymFnEq fn1 fn2 of
          Just PC.Refl -> case PC.testEquality args1 args2 of
            Just PC.Refl -> Just PC.Refl
            Nothing -> Nothing
          Nothing -> Nothing
      (FnApp {}, _) -> Nothing

instance
  ( TestEquality f
  ) => Eq (App t f tp) where
  x == y = PC.isJust (testEquality x y)

$(return [])

instance (PC.OrdF f, Eq (f BT.BaseBoolType), Ord (f BT.BaseBoolType)) => PC.OrdF (App t f) where
  compareF = $(PTH.structuralTypeOrd [t| App |]
    [ (PTH.TypeApp (PTH.TypeApp (PTH.ConType [t| WE.ExprBoundVar |]) PTH.AnyType) PTH.AnyType,
       [| PC.compareF |])
    , (PTH.TypeApp (PTH.TypeApp (PTH.ConType [t| EBV.BVExpr |]) PTH.AnyType) PTH.AnyType,
       [| PC.compareF |])
    , (PTH.TypeApp (PTH.TypeApp (PTH.ConType [t| EL.LogicExpr |]) PTH.AnyType) PTH.AnyType,
       [| PC.compareF |])
    , (PTH.TypeApp (PTH.TypeApp (PTH.ConType [t| Ctx.Assignment |]) PTH.AnyType) PTH.AnyType,
       [| PC.compareF |])
    , (PTH.TypeApp (PTH.TypeApp (PTH.TypeApp (PTH.TypeApp (PTH.ConType [t| ESF.SymFn |]) PTH.AnyType) PTH.AnyType) PTH.AnyType) PTH.AnyType,
       [| ESF.compareSymFn |])
    ])

instance
  ( PC.OrdF f
  , Eq (f BT.BaseBoolType)
  , Ord (f BT.BaseBoolType)
  ) => Ord (App t f tp) where
  compare x y = PC.toOrdering (PC.compareF x y)

-- | Pretty-print an App given a pretty-printer for the term functor
pretty :: (forall tp'. f tp' -> PP.Doc ann) -> App t f tp -> PP.Doc ann
pretty ppF = \case
  BoundVarApp bv -> PP.pretty (show (WE.bvarName bv))
  BVApp bvExpr -> EBV.pretty ppF bvExpr
  LogicApp logicExpr -> EL.pretty ppF logicExpr
  FnApp fn args ->
    PP.parens $ PP.hsep
      [ PP.pretty (show (ESF.symFnName fn))
      , PP.hsep (TFC.toListFC ppF args)
      ]
