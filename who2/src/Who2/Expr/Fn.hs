{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Expr.Fn
  ( applyFn
  ) where

import qualified Data.Parameterized.Context as Ctx

import qualified What4.Interface as WI
import qualified What4.Utils.AbstractDomains as AD

import Who2.Expr (Expr)
import qualified Who2.Expr as E
import qualified Who2.Expr.App as EA
import qualified Who2.Expr.SymExpr as ESE
import qualified Who2.Expr.SymFn as ESF
import qualified Who2.Expr.Subst as Subst

-- | Apply a symbolic function to arguments
-- Takes both an alloc function (for uninterpreted functions) and a builder (for defined functions)
applyFn ::
  ( WI.IsSymExprBuilder sym
  , WI.SymExpr sym ~ ESE.SymExpr t
  , WI.SymFn sym ~ ESF.SymFn t (E.Expr t (EA.App t))
  ) =>
  (forall tp. EA.App t (Expr t (EA.App t)) tp -> AD.AbstractValue tp -> IO (Expr t (EA.App t) tp)) ->
  sym ->
  ESF.SymFn t (E.Expr t (EA.App t)) args ret ->
  Ctx.Assignment (E.Expr t (EA.App t)) args ->
  IO (E.Expr t (EA.App t) ret)
applyFn alloc sym fn args =
  case ESF.symFnInfo fn of
    ESF.UninterpFnInfo _ retType ->
      -- For uninterpreted functions, just allocate a new FnApp expression
      -- with an unconstrained abstract value (we know nothing about the result)
      alloc (EA.FnApp fn args) (AD.avTop retType)

    ESF.DefinedFnInfo vars body _policy _retType ->
      -- For defined functions with AlwaysUnfold policy, substitute formal
      -- parameters with actual arguments in the function body
      -- Use builder methods to maintain expression invariants
      Subst.substBoundVarsInFn sym body vars args
