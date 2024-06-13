-----------------------------------------------------------------------
-- |
-- Module           : What4.Concretize
-- Description      : Concretize values
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module What4.Concretize
  ( ConcretizationFailure(..)
  , concretize
  ) where

import Control.Monad (forM)

import qualified What4.Expr.Builder as WEB
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat

-- | Reasons why attempting to resolve a symbolic expression as concrete can
-- fail.
data ConcretizationFailure
  = SolverUnknown
    -- ^ Querying the SMT solver yielded @UNKNOWN@.
  | UnsatInitialAssumptions
    -- ^ Querying the SMT solver for an initial model of the expression failed
    -- due to the initial assumptions in scope being unsatisfiable.
  | MultipleModels
    -- ^ There are multiple possible models for the expression, which means it
    -- is truly symbolic and therefore unable to be concretized.
  deriving Show

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using an
-- online SMT solver connection.
--
-- The implementation of this function asks for a model from the solver. If it
-- gets one, it adds a blocking clause and asks for another. If there was only
-- one model, concretize the initial value and return it with 'Right'.
-- Otherwise, return an explanation of why concretization failed with 'Left'.
concretize ::
  ( sym ~ WEB.ExprBuilder scope st fs
  , WPO.OnlineSolver solver
  ) =>
  -- | The symbolic backend
  sym ->
  WPO.SolverProcess scope solver ->
  -- | The symbolic term to concretize
  WI.SymExpr sym tp ->
  IO (Either ConcretizationFailure (WEG.GroundValue tp))
concretize sym sp val =
  case WEG.asGround val of
    Just gVal -> pure (Right gVal)
    Nothing -> do
      -- First, check to see if there is a model of the symbolic value.
      res <- WPO.inNewFrame sp $ do
        msat <- WPO.checkAndGetModel sp "Concretize value (with no assumptions)"
        mmodel <- case msat of
          WSat.Unknown -> pure $ Left SolverUnknown
          WSat.Unsat {} -> pure $ Left UnsatInitialAssumptions
          WSat.Sat mdl -> pure $ Right mdl
        forM mmodel $ \mdl -> WEG.groundEval mdl val
      case res of
        Left _failure -> pure res -- We failed to get a model
        Right concVal -> do
          -- We found a model, so check to see if this is the only possible
          -- model for this symbolic value.  We do this by adding a blocking
          -- clause that assumes the SymBV is /not/ equal to the model we
          -- found in the previous step. If this is unsatisfiable, the SymBV
          -- can only be equal to that model, so we can conclude it is
          -- concrete. If it is satisfiable, on the other hand, the SymBV can
          -- be multiple values, so it is truly symbolic.
          WPO.inNewFrame sp $ do
            injectedConcVal <- WEG.groundToSym sym (WI.exprType val) concVal
            eq <- WI.isEq sym val injectedConcVal
            block <- WI.notPred sym eq
            WPS.assume (WPO.solverConn sp) block
            msat <- WPO.checkAndGetModel sp "Concretize value (with blocking clause)"
            case msat of
              WSat.Unknown -> pure $ Left SolverUnknown -- Total failure
              WSat.Sat _mdl -> pure $ Left MultipleModels  -- There are multiple models
              WSat.Unsat {} -> pure res -- There is a single concrete result
