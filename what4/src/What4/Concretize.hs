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
  , UniqueConcretizationFailure(..)
  , uniquelyConcretize
  ) where

import qualified What4.Expr.Builder as WEB
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat

-- | Reasons why attempting to resolve a symbolic expression as ground can fail.
data ConcretizationFailure
  = SolverUnknown
    -- ^ Querying the SMT solver yielded @UNKNOWN@.
  | UnsatInitialAssumptions
    -- ^ Querying the SMT solver for an initial model of the expression failed
    -- due to the initial assumptions in scope being unsatisfiable.
  deriving Show

-- | Get a 'WEG.GroundValue' for a 'WI.SymExpr' by asking an online solver for
-- a model.
--
-- In contrast with 'uniquelyConcretize', this function returns the value of the
-- 'WI.SymExpr' in just one of potentially many distinct models. See the Haddock
-- on 'uniquelyConcretize' for a further comparison.
concretize ::
  ( sym ~ WEB.ExprBuilder scope st fs
  , WPO.OnlineSolver solver
  ) =>
  WPO.SolverProcess scope solver ->
  -- | The symbolic term to query from the model
  WI.SymExpr sym tp ->
  IO (Either ConcretizationFailure (WEG.GroundValue tp))
concretize sp val =
  case WEG.asGround val of
    Just gVal -> pure (Right gVal)
    Nothing -> do
      WPO.inNewFrame sp $ do
        msat <- WPO.checkAndGetModel sp "Ground value using model"
        case msat of
          WSat.Unknown -> pure $ Left SolverUnknown
          WSat.Unsat {} -> pure $ Left UnsatInitialAssumptions
          WSat.Sat mdl -> Right <$> WEG.groundEval mdl val

data UniqueConcretizationFailure
  = GroundingFailure ConcretizationFailure
  | MultipleModels
    -- ^ There are multiple possible models for the expression, which means it
    -- is truly symbolic and therefore unable to be concretized.
  deriving Show

-- | Attempt to resolve the given 'WI.SymExpr' to a unique concrete value using
-- an online SMT solver connection.
--
-- The implementation of this function (1) asks for a model from the solver.
-- If it gets one, it (2) adds a blocking clause and asks for another. If there
-- was only one model, concretize the initial value and return it with 'Right'.
-- Otherwise, return an explanation of why concretization failed with 'Left'.
-- This behavior is contrasted with 'concretize', which just does (1).
uniquelyConcretize ::
  ( sym ~ WEB.ExprBuilder scope st fs
  , WPO.OnlineSolver solver
  ) =>
  -- | The symbolic backend
  sym ->
  WPO.SolverProcess scope solver ->
  -- | The symbolic term to concretize
  WI.SymExpr sym tp ->
  IO (Either UniqueConcretizationFailure (WEG.GroundValue tp))
uniquelyConcretize sym sp val =
  case WEG.asGround val of
    Just gVal -> pure (Right gVal)
    Nothing -> do
      -- First, check to see if there is a model of the symbolic value.
      concVal_ <- concretize sp val
      case concVal_ of
        Left e -> pure (Left (GroundingFailure e))
        Right concVal -> do
          -- We found a model, so check to see if this is the only possible
          -- model for this symbolic value.  We do this by adding a blocking
          -- clause that assumes the `SymExpr` is /not/ equal to the model we
          -- found in the previous step. If this is unsatisfiable, the SymExpr
          -- can only be equal to that model, so we can conclude it is concrete.
          -- If it is satisfiable, on the other hand, the `SymExpr` can be
          -- multiple values, so it is truly symbolic.
          WPO.inNewFrame sp $ do
            injectedConcVal <- WEG.groundToSym sym (WI.exprType val) concVal
            eq <- WI.isEq sym val injectedConcVal
            block <- WI.notPred sym eq
            WPS.assume (WPO.solverConn sp) block
            msat' <- WPO.checkAndGetModel sp "Concretize value (with blocking clause)"
            case msat' of
              WSat.Unknown -> pure $ Left $ GroundingFailure $ SolverUnknown
              WSat.Sat _mdl -> pure $ Left $ MultipleModels
              WSat.Unsat {} -> pure $ Right concVal -- There is a single concrete result
