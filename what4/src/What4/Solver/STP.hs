------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.STP
-- Description : Solver adapter code for STP
-- Copyright   : (c) Galois, Inc 2015-2020
-- License     : BSD3
-- Maintainer  : Joe Hendrix <rdockins@galois.com>
-- Stability   : provisional
--
-- STP-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module What4.Solver.STP
  ( STP(..)
  , stpAdapter
  , stpPath
  , stpOptions
  , stpFeatures
  , runSTPInOverride
  , withSTP
  ) where

import           Data.Bits

import           What4.BaseTypes
import           What4.Config
import           What4.Concrete
import           What4.Interface
import           What4.ProblemFeatures
import           What4.SatResult
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Solver.Adapter
import           What4.Protocol.Online
import qualified What4.Protocol.SMTLib2 as SMT2
import           What4.Utils.Process

data STP = STP deriving Show

-- | Path to stp
stpPath :: ConfigOption (BaseStringType Unicode)
stpPath = configOption knownRepr "solver.stp.path"

stpPathOLD :: ConfigOption (BaseStringType Unicode)
stpPathOLD = configOption knownRepr "stp_path"

stpRandomSeed :: ConfigOption BaseIntegerType
stpRandomSeed = configOption knownRepr "solver.stp.random-seed"

stpRandomSeedOLD :: ConfigOption BaseIntegerType
stpRandomSeedOLD = configOption knownRepr "stp.random-seed"

intWithRangeOpt :: ConfigOption BaseIntegerType -> Integer -> Integer -> ConfigDesc
intWithRangeOpt nm lo hi = mkOpt nm sty Nothing Nothing
  where sty = integerWithRangeOptSty (Inclusive lo) (Inclusive hi)

stpOptions :: [ConfigDesc]
stpOptions =
  let mkPath co = mkOpt co
                  executablePathOptSty
                  (Just "Path to STP executable.")
                  (Just (ConcreteString "stp"))
      p1 = mkPath stpPath
      r1 = intWithRangeOpt stpRandomSeed (negate (2^(30::Int)-1)) (2^(30::Int)-1)
  in [ p1, r1
     , deprecatedOpt [p1] $ mkPath stpPathOLD
     , deprecatedOpt [r1] $ intWithRangeOpt stpRandomSeedOLD
       (negate (2^(30::Int)-1)) (2^(30::Int)-1)
     ] <> SMT2.smtlib2Options

stpAdapter :: SolverAdapter st
stpAdapter =
  SolverAdapter
  { solver_adapter_name = "stp"
  , solver_adapter_config_options = stpOptions
  , solver_adapter_check_sat  = runSTPInOverride
  , solver_adapter_write_smt2 =
       SMT2.writeDefaultSMT2 STP "STP" defaultWriteSMTLIB2Features
  }

instance SMT2.SMTLib2Tweaks STP where
  smtlib2tweaks = STP

instance SMT2.SMTLib2GenericSolver STP where
  defaultSolverPath _ = findSolverPath stpPath . getConfiguration

  defaultSolverArgs _ _ = return ["--SMTLIB2"]

  defaultFeatures _ = stpFeatures

  setDefaultLogicAndOptions writer = do
    SMT2.setProduceModels writer True
    SMT2.setLogic writer SMT2.qf_bv


stpFeatures :: ProblemFeatures
stpFeatures = useIntegerArithmetic .|. useBitvectors

runSTPInOverride
  :: ExprBuilder t st fs
  -> LogData
  -> [BoolExpr t]
  -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
  -> IO a
runSTPInOverride = SMT2.runSolverInOverride STP SMT2.nullAcknowledgementAction (SMT2.defaultFeatures STP)

-- | Run STP in a session. STP will be configured to produce models, buth
-- otherwise left with the default configuration.
withSTP
  :: ExprBuilder t st fs
  -> FilePath
    -- ^ Path to STP executable
  -> LogData
  -> (SMT2.Session t STP -> IO a)
    -- ^ Action to run
  -> IO a
withSTP = SMT2.withSolver STP SMT2.nullAcknowledgementAction (SMT2.defaultFeatures STP)

setInteractiveLogicAndOptions ::
  SMT2.SMTLib2Tweaks a =>
  SMT2.WriterConn t (SMT2.Writer a) ->
  IO ()
setInteractiveLogicAndOptions writer = do
    -- Tell STP to acknowledge successful commands
    SMT2.setOption writer "print-success"  "true"
    -- Tell STP to produce models
    SMT2.setOption writer "produce-models" "true"

    -- Tell STP to make declaraions global, so they are not removed by 'pop' commands
-- TODO, add this command once https://github.com/stp/stp/issues/365 is closed
--    SMT2.setOption writer "global-declarations" "true"

instance OnlineSolver (SMT2.Writer STP) where
  startSolverProcess = SMT2.startSolver STP SMT2.smtAckResult setInteractiveLogicAndOptions
  shutdownSolverProcess = SMT2.shutdownSolver STP
