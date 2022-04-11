{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : What4.TransitionSystem
-- Description : Definition of a transition system made of What4 expressions
-- Copyright   : (c) Galois Inc, 2020-2021
-- License     : BSD3
-- Maintainer  : val@galois.com
-- |
module What4.TransitionSystem
  ( CtxState,
    TransitionSystem (..),
    createStateStruct,
    makeInitialState,
    makeQueries,
    makeTransitions,
    userSymbol',
  )
where

import qualified Control.Lens as L
import Control.Monad.Identity (forM)
import Data.Functor.Const (Const (..))
import qualified Data.Parameterized.Context as Ctx
import qualified What4.BaseTypes as BaseTypes
import What4.Expr (ExprBuilder)
import qualified What4.Interface as What4
import Prelude hiding (init)

-- | Convenient wrapper around @What4.userSymbol@ for when we're willing to fail
-- on error.
userSymbol' :: String -> What4.SolverSymbol
userSymbol' s = case What4.userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

-- | @TransitionSystem@ can be used to describe a transition system, which can
-- then be elaborated into a set of SMT formulas.
data TransitionSystem sym state = TransitionSystem
  { -- | Representations for the fields of the state type, can be computed
    -- automatically using @knownRepr@ for a concrete type parameter @state@.
    stateReprs :: Ctx.Assignment BaseTypes.BaseTypeRepr state,
    -- | Names of the field accessor for each state field.
    stateNames :: Ctx.Assignment (Const What4.SolverSymbol) state,
    -- | Initial state predicate.
    initialStatePredicate ::
      What4.SymStruct sym state ->
      IO (What4.Pred sym),
    -- | Binary relations over states for the transition, parameterized by the
    -- current state and the next state.  Should return a name for each
    -- transition, and their boolean formula.
    stateTransitions ::
      What4.SymStruct sym state ->
      What4.SymStruct sym state ->
      IO [(What4.SolverSymbol, What4.Pred sym)],
    -- | Queries that must hold at all states.
    queries ::
      What4.SymStruct sym state ->
      IO [What4.Pred sym]
  }

createStateStruct ::
  What4.IsSymExprBuilder sym =>
  sym ->
  -- | Namespace of the state structure.
  String ->
  Ctx.Assignment BaseTypes.BaseTypeRepr state ->
  IO (What4.SymStruct sym state)
createStateStruct sym namespace stateType =
  What4.freshConstant sym (userSymbol' namespace) (What4.BaseStructRepr stateType)

-- Actually I think it'll be better to have a fresh struct rather than having fields
-- What4.mkStruct sym =<< freshStateVars sym namespace stateType

-- | A context with just one field, a struct type for the state.
type CtxState state = Ctx.EmptyCtx Ctx.::> BaseTypes.BaseStructType state

-- | Computes a set of side conditions we must add to state formulas to account
-- for the mismatch between What4 types and types found in transition systems
-- such as MCMT and Sally.  For instance, a What4 @Nat@ must be translated as
-- an MCMT @Int@ (since MCMT does not have natural numbers), with a side
-- condition of positivity.
sideConditions ::
  forall sym t st fs state.
  sym ~ ExprBuilder t st fs =>
  sym ->
  -- | state type
  Ctx.Assignment BaseTypes.BaseTypeRepr state ->
  -- | state on which to operate
  What4.SymStruct sym state ->
  IO (What4.Pred sym)
sideConditions sym stateReprs _state =
  do
    preds <- Ctx.traverseAndCollect sideConditionsForIndex stateReprs
    What4.andAllOf sym L.folded preds
  where
    sideConditionsForIndex ::
      Ctx.Index state tp ->
      BaseTypes.BaseTypeRepr tp ->
      IO [What4.Pred sym]
    sideConditionsForIndex _ BaseTypes.BaseBoolRepr = return []
    sideConditionsForIndex _ BaseTypes.BaseIntegerRepr = return []
    sideConditionsForIndex _ BaseTypes.BaseRealRepr = return []
    sideConditionsForIndex _ (BaseTypes.BaseBVRepr _) = return []
    sideConditionsForIndex _ bt =
      error $ "sideConditions: Not implemented for base type " ++ show bt ++ ". Please report."

makeInitialState ::
  sym ~ ExprBuilder t st fs =>
  sym ->
  TransitionSystem sym state ->
  IO (What4.Pred sym)
makeInitialState sym (TransitionSystem {initialStatePredicate, stateReprs}) =
  do
    init <- createStateStruct sym "init" stateReprs
    initP <- initialStatePredicate init
    sideP <- sideConditions sym stateReprs init
    What4.andPred sym initP sideP

makeTransitions ::
  sym ~ ExprBuilder t st fs =>
  sym ->
  -- | Name to use for the "main" transition.
  What4.SolverSymbol ->
  -- | Exporter-specific transition builder of transition, receiving as input
  -- the name of that transition and the transition predicate.
  (What4.SolverSymbol -> What4.Pred sym -> transition) ->
  TransitionSystem sym state ->
  IO [transition]
makeTransitions
  sym
  mainTransitionName
  makeTransition
  (TransitionSystem {stateReprs, stateTransitions}) =
    do
      state <- createStateStruct sym "state" stateReprs
      next <- createStateStruct sym "next" stateReprs
      transitions <- stateTransitions state next
      allTransitions <- forM transitions $ \(name, transitionP) ->
        do
          stateSideP <- sideConditions sym stateReprs state
          nextSideP <- sideConditions sym stateReprs next
          transitionRelation <- What4.andAllOf sym L.folded [transitionP, stateSideP, nextSideP]
          return $ makeTransition name transitionRelation
      -- the main transition is the conjunction of all transitions
      -- FIXME: turn the name of the transition into an expression
      transitionsPreds <- forM (fst <$> transitions) $ \transitionName ->
        What4.freshConstant sym transitionName BaseTypes.BaseBoolRepr
      transitionRelation <- What4.orOneOf sym L.folded transitionsPreds
      let mainTransition = makeTransition mainTransitionName transitionRelation
      -- A transition may only refer to previously-defined transitions, so
      -- @mainTransition@ must be last.
      return (allTransitions ++ [mainTransition])

makeQueries ::
  sym ~ ExprBuilder t st fs =>
  sym ->
  (What4.Pred sym -> query) ->
  TransitionSystem sym state ->
  IO [query]
makeQueries
  sym
  makeQuery
  (TransitionSystem {queries, stateReprs}) =
    do
      -- NOTE: Event though some backend queries do not use a namespace, we need
      -- to use a "query" namespace here, as it forces the What4 backend to
      -- treat those fields as different from the "state"/"next" ones.
      queryState <- createStateStruct sym "query" stateReprs
      (makeQuery <$>) <$> queries queryState
