{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : What4.TransitionSystem.Exporter.Sally
-- Description : Export What4 transition system to the Sally format
-- Copyright   : (c) Galois Inc, 2020-2021
-- License     : BSD3
-- Maintainer  : val@galois.com
module What4.TransitionSystem.Exporter.Sally
  ( exportTransitionSystem,
    mySallyNames,
  )
where

import qualified Data.Parameterized.Context as Ctx
import qualified Language.Sally as S
import What4.Expr (ExprBuilder)
import qualified What4.Interface as What4
import qualified What4.TransitionSystem as TS
import Prelude hiding (init)

data SallyNames = SallyNames
  { -- | Name of the initial state predicate
    initialName :: S.Name,
    -- | Name of the main transition
    mainTransitionName :: S.Name,
    -- | Name of the state type
    stateName :: S.Name,
    -- | Name of the transition system
    systemName :: S.Name
  }

-- | @mySallyNames@ has some default names since we currently don't care too
-- much about changing them
mySallyNames :: SallyNames
mySallyNames =
  SallyNames
    { initialName = TS.userSymbol' "InitialState",
      mainTransitionName = TS.userSymbol' "MainTransition",
      stateName = TS.userSymbol' "State",
      systemName = TS.userSymbol' "System"
    }

sallyState ::
  SallyNames ->
  TS.TransitionSystem sym stateType ->
  S.SallyState stateType Ctx.EmptyCtx
sallyState
  (SallyNames {stateName})
  (TS.TransitionSystem {TS.stateNames, TS.stateReprs}) =
    S.SallyState
      { S.sallyStateName = stateName,
        S.sallyStateVars = stateReprs,
        S.sallyStateVarsNames = stateNames,
        S.sallyStateInputs = Ctx.Empty,
        S.sallyStateInputsNames = Ctx.Empty
      }

sallyQuery :: S.Name -> What4.Pred (ExprBuilder t st fs) -> S.SallyQuery t
sallyQuery systemName sallyQueryPredicate =
  S.SallyQuery
    { S.sallyQuerySystemName = systemName,
      -- sqLet = [],
      S.sallyQueryPredicate,
      S.sallyQueryComment = ""
    }

exportTransitionSystem ::
  ExprBuilder t st fs ->
  SallyNames ->
  TS.TransitionSystem (ExprBuilder t st fs) stateType ->
  IO (S.Sally t stateType Ctx.EmptyCtx Ctx.EmptyCtx)
exportTransitionSystem
  sym
  (sn@SallyNames {initialName, mainTransitionName, stateName, systemName})
  ts =
    do
      sallyStateFormulaPredicate <- TS.makeInitialState sym ts
      sallyTransitions <-
        TS.makeTransitions
          sym
          mainTransitionName
          (S.SallyTransition stateName)
          ts
      sallyQueries <- TS.makeQueries sym (sallyQuery systemName) ts
      let sallyInitialFormula =
            S.SallyStateFormula
              { S.sallyStateFormulaName = initialName,
                S.sallyStateFormulaDomain = stateName,
                S.sallyStateFormulaPredicate
              }
      let sallySystem =
            S.SallySystem
              { S.sallySystemName = systemName,
                S.sallySystemStateName = stateName,
                S.sallySystemInitialStateName = initialName,
                S.sallySystemTransitionName = mainTransitionName
              }
      return $
        S.Sally
          { S.sallyState = sallyState sn ts,
            S.sallyFormulas = [],
            S.sallyConstants = Ctx.Empty,
            S.sallyInitialFormula,
            S.sallyTransitions,
            S.sallySystem,
            S.sallyQueries
          }
