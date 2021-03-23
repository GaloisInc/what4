{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | TODO
module What4.TransitionSystem
  ( CtxState,
    TransitionSystem (..),
    createStateStruct,
    mySallyNames,
    -- stateField,
    transitionSystemToSally,
    userSymbol',
  )
where

import qualified Control.Lens as L
import Control.Monad.Identity
import Data.Functor.Const (Const (..))
import qualified Data.Parameterized.Context as Ctx
import qualified Language.Sally as S
import What4.BaseTypes
import What4.Expr
import qualified What4.Interface as What4
import Prelude hiding (init)

userSymbol' :: String -> What4.SolverSymbol
userSymbol' s = case What4.userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

-- | @TransitionSystem@ can be used to describe a transition system, which can
-- then be elaborated into a set of SMT formulas.  We try to have this type
-- **not** depend on Sally.
data TransitionSystem sym state = TransitionSystem
  { -- | representations for the fields of the state type, can be computed
    -- automatically using @knownRepr@ for a concrete value of @state@
    stateReprs :: Ctx.Assignment BaseTypeRepr state,
    -- | names of the field accessor for each state field
    stateNames :: Ctx.Assignment (Const What4.SolverSymbol) state,
    -- | initial state predicate
    initialStatePredicate ::
      What4.SymStruct sym state ->
      IO (What4.Pred sym),
    -- | Binary relations over states for the transition, parameterized by
    -- the current state and the next state.  Returns a name for each
    -- transition, and their boolean formula.
    -- NOTE: it is now important that each transition receives its own,
    -- fresh copy of the state structs, so that What4 knows not to try and
    -- share them, and to declare them in each Sally transition.
    stateTransitions ::
      What4.SymStruct sym state ->
      What4.SymStruct sym state ->
      IO [(S.Name, What4.Pred sym)],
    -- | Sally queries that must hold at all states
    --
    -- It may seem surprising that it receives a state, since Sally queries are
    -- not namespaced.  The issue is, if we don't namespace the fields
    -- corresponding to the arguments of the block that the query refers to,
    -- they will be anonymized by the SMTWriter.
    --
    -- By creating the "query" state struct, the fields will be namespaced as
    -- "query.field".  We can detect those fields in the writer (just as we do
    -- for the "init" namespace, that must exist for What4 but must be erased
    -- for Sally), and remove the field access as we print.
    queries ::
      What4.SymStruct sym state ->
      IO [What4.Pred sym]
  }

data SallyNames = SallyNames
  { -- | name of the initial state predicate
    initialName :: S.Name,
    -- | name of the main transition
    mainTransitionName :: S.Name,
    -- | name of the state type
    stateName :: S.Name,
    -- | name of the transition system
    systemName :: S.Name
  }

-- | @mySallyNames@ has some default names since we currently don't care too
-- much about changing them
mySallyNames :: SallyNames
mySallyNames =
  SallyNames
    { initialName = userSymbol' "InitialState",
      mainTransitionName = userSymbol' "MainTransition",
      stateName = userSymbol' "State",
      systemName = userSymbol' "System"
    }

sallyState ::
  SallyNames ->
  TransitionSystem sym stateType ->
  S.SallyState stateType Ctx.EmptyCtx
sallyState
  SallyNames
    { stateName
    }
  TransitionSystem
    { stateNames,
      stateReprs
    } =
    S.SallyState
      { S.sallyStateName = stateName,
        S.sallyStateVars = stateReprs,
        S.sallyStateVarsNames = stateNames,
        S.sallyStateInputs = Ctx.Empty,
        S.sallyStateInputsNames = Ctx.Empty
      }

-- | Computes a set of side conditions we must add to state formulas to account
-- for the mismatch between What4 types and sally types.  For instance, a What4
-- @Nat@ must be translated as a Sally @Int@ (since Sally does not have natural
-- numbers), with a side condition of positivity.
sideConditions ::
  forall t st fs state.
  ExprBuilder t st fs ->
  -- | state type
  Ctx.Assignment BaseTypeRepr state ->
  -- | state on which to operate
  What4.SymStruct (ExprBuilder t st fs) state ->
  IO (S.SallyPred t)
sideConditions sym stateReprs state =
  do
    preds <- Ctx.traverseAndCollect sideConditionsForIndex stateReprs
    What4.andAllOf sym L.folded preds
  where
    sideConditionsForIndex :: Ctx.Index state tp -> BaseTypeRepr tp -> IO [S.SallyPred t]
    sideConditionsForIndex _ BaseBoolRepr = return []
    sideConditionsForIndex _ BaseIntegerRepr = return []
    sideConditionsForIndex _ BaseRealRepr = return []
    sideConditionsForIndex _ (BaseBVRepr _) = return []
    sideConditionsForIndex _ bt = error $ "sideConditions: Not implemented for base type " ++ show bt ++ ". Please report."

createStateStruct ::
  What4.IsSymExprBuilder sym =>
  sym ->
  String ->
  Ctx.Assignment BaseTypeRepr state ->
  IO (What4.SymStruct sym state)
createStateStruct sym namespace stateType =
  What4.freshConstant sym (userSymbol' namespace) (What4.BaseStructRepr stateType)

-- actually I think it'll be better to have a fresh struct rather than having fields
-- What4.mkStruct sym =<< freshStateVars sym namespace stateType

sallyInitialState ::
  ExprBuilder t st fs ->
  TransitionSystem (ExprBuilder t st fs) state ->
  IO (S.SallyPred t)
sallyInitialState
  sym
  TransitionSystem
    { initialStatePredicate,
      stateReprs
    } =
    do
      init <- createStateStruct sym "init" stateReprs
      initP <- initialStatePredicate init
      sideP <- sideConditions sym stateReprs init
      What4.andPred sym initP sideP

makeSallyTransitions ::
  ExprBuilder t st fs ->
  SallyNames ->
  TransitionSystem (ExprBuilder t st fs) state ->
  IO [S.SallyTransition t]
makeSallyTransitions
  sym
  ( SallyNames
      { mainTransitionName,
        stateName
      }
    )
  ( TransitionSystem
      { stateReprs,
        stateTransitions
      }
    ) =
    do
      state <- createStateStruct sym "state" stateReprs
      next <- createStateStruct sym "next" stateReprs
      transitions <- stateTransitions state next
      allTransitions <- forM transitions $ \(name, transitionP) ->
        do
          stateSideP <- sideConditions sym stateReprs state
          nextSideP <- sideConditions sym stateReprs next
          transitionRelation <- What4.andAllOf sym L.folded [transitionP, stateSideP, nextSideP]
          return $
            S.SallyTransition
              { S.transitionName = name,
                S.transitionDomain = stateName,
                -- traLet = [],
                S.transitionRelation
              }
      -- the main transition is the conjunction of all transitions
      -- FIXME: turn the name of the transition into an expression
      transitionsPreds <- forM (S.transitionName <$> allTransitions) $ \transitionName ->
        What4.freshConstant sym transitionName BaseBoolRepr
      transitionRelation <- What4.orOneOf sym L.folded transitionsPreds
      let mainTransition =
            S.SallyTransition
              { S.transitionName = mainTransitionName,
                S.transitionDomain = stateName,
                -- traLet = [],
                S.transitionRelation
              }
      -- a transition may only refer to previously-defined transitions, so
      -- @mainTransition@ must be last
      return (allTransitions ++ [mainTransition])

makeSallyQueries ::
  sym ~ ExprBuilder t st fs =>
  sym ->
  SallyNames ->
  TransitionSystem sym state ->
  IO [S.SallyQuery t]
makeSallyQueries sym
  SallyNames {systemName }
  TransitionSystem { queries, stateReprs }
  = do
  queryState <- createStateStruct sym "query" stateReprs
  map (sallyQuery systemName) <$> queries queryState

sallyQuery :: S.Name -> What4.Pred (ExprBuilder t st fs) -> S.SallyQuery t
sallyQuery systemName sallyQueryPredicate =
  S.SallyQuery
    { S.sallyQuerySystemName = systemName,
      -- sqLet = [],
      S.sallyQueryPredicate,
      S.sallyQueryComment = ""
    }

transitionSystemToSally ::
  ExprBuilder t st fs ->
  SallyNames ->
  TransitionSystem (ExprBuilder t st fs) stateType ->
  IO (S.Sally t stateType Ctx.EmptyCtx Ctx.EmptyCtx)
transitionSystemToSally
  sym
  sn@SallyNames
    { initialName,
      mainTransitionName,
      stateName,
      systemName
    }
  ts =
    do
      sallyStateFormulaPredicate <- sallyInitialState sym ts
      sallyTransitions <- makeSallyTransitions sym sn ts
      sallyQueries <- makeSallyQueries sym sn ts
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

-- | A context with just one field, a struct type for the state
type CtxState state = Ctx.EmptyCtx Ctx.::> BaseStructType state
