------------------------------------------------------------------------
-- |
-- Module           : What4.Solver.Boolector
-- Description      : Interface for running Boolector
-- Copyright        : (c) Galois, Inc 2014-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an interface for running Boolector and parsing
-- the results back.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module What4.Solver.Boolector
  ( Boolector(..)
  , boolectorPath
  , boolectorTimeout
  , boolectorOptions
  , boolectorAdapter
  , runBoolectorInOverride
  , withBoolector
  , boolectorFeatures
  ) where

import           Control.Monad
import           Data.Bits ( (.|.) )

import           What4.BaseTypes
import           What4.Concrete
import           What4.Config
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Interface
import           What4.ProblemFeatures
import           What4.Protocol.Online
import qualified What4.Protocol.SMTLib2 as SMT2
import           What4.Protocol.SMTLib2.Response ( strictSMTParseOpt )
import           What4.SatResult
import           What4.Solver.Adapter
import           What4.Utils.Process


data Boolector = Boolector deriving Show

-- | Path to boolector
boolectorPath :: ConfigOption (BaseStringType Unicode)
boolectorPath = configOption knownRepr "solver.boolector.path"

boolectorPathOLD :: ConfigOption (BaseStringType Unicode)
boolectorPathOLD = configOption knownRepr "boolector_path"

-- | Per-check timeout, in milliseconds (zero is none)
boolectorTimeout :: ConfigOption BaseIntegerType
boolectorTimeout = configOption knownRepr "solver.boolector.timeout"

-- | Control strict parsing for Boolector solver responses (defaults
-- to solver.strict-parsing option setting).
boolectorStrictParsing :: ConfigOption BaseBoolType
boolectorStrictParsing = configOption knownRepr "solver.boolector.strict_parsing"

boolectorOptions :: [ConfigDesc]
boolectorOptions =
  let bpOpt co = mkOpt
                 co
                 executablePathOptSty
                 (Just "Path to boolector executable")
                 (Just (ConcreteString "boolector"))
      mkTmo co = mkOpt co
                 integerOptSty
                 (Just "Per-check timeout in milliseconds (zero is none)")
                 (Just (ConcreteInteger 0))
      bp = bpOpt boolectorPath
      bp2 = deprecatedOpt [bp] $ bpOpt boolectorPathOLD
  in [ bp, bp2
     , mkTmo boolectorTimeout
     , copyOpt (const $ configOptionText boolectorStrictParsing) strictSMTParseOpt
     ] <> SMT2.smtlib2Options

boolectorAdapter :: SolverAdapter st
boolectorAdapter =
  SolverAdapter
  { solver_adapter_name = "boolector"
  , solver_adapter_config_options = boolectorOptions
  , solver_adapter_check_sat = runBoolectorInOverride
  , solver_adapter_write_smt2 =
      SMT2.writeDefaultSMT2 () "Boolector" defaultWriteSMTLIB2Features
      (Just boolectorStrictParsing)
  }

instance SMT2.SMTLib2Tweaks Boolector where
  smtlib2tweaks = Boolector

runBoolectorInOverride ::
  ExprBuilder t st fs ->
  LogData ->
  [BoolExpr t] ->
  (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a) ->
  IO a
runBoolectorInOverride =
  SMT2.runSolverInOverride Boolector SMT2.nullAcknowledgementAction
  boolectorFeatures (Just boolectorStrictParsing)

-- | Run Boolector in a session. Boolector will be configured to produce models, but
-- otherwise left with the default configuration.
withBoolector
  :: ExprBuilder t st fs
  -> FilePath
    -- ^ Path to Boolector executable
  -> LogData
  -> (SMT2.Session t Boolector -> IO a)
    -- ^ Action to run
  -> IO a
withBoolector = SMT2.withSolver Boolector SMT2.nullAcknowledgementAction
                boolectorFeatures (Just boolectorStrictParsing)


boolectorFeatures :: ProblemFeatures
boolectorFeatures = useSymbolicArrays
                .|. useBitvectors

instance SMT2.SMTLib2GenericSolver Boolector where
  defaultSolverPath _ = findSolverPath boolectorPath . getConfiguration
  defaultSolverArgs _ _ = return ["--smt2", "--smt2-model", "--incremental", "--output-format=smt2", "-e=0"]
  defaultFeatures _ = boolectorFeatures
  setDefaultLogicAndOptions writer = do
    SMT2.setLogic writer SMT2.allSupported
    SMT2.setProduceModels writer True

setInteractiveLogicAndOptions ::
  SMT2.SMTLib2Tweaks a =>
  SMT2.WriterConn t (SMT2.Writer a) ->
  IO ()
setInteractiveLogicAndOptions writer = do
    SMT2.setOption writer "print-success"  "true"
    SMT2.setOption writer "produce-models" "true"
    SMT2.setOption writer "global-declarations" "true"
    when (SMT2.supportedFeatures writer `hasProblemFeature` useUnsatCores) $ do
      SMT2.setOption writer "produce-unsat-cores" "true"
    SMT2.setLogic writer SMT2.allSupported

instance OnlineSolver (SMT2.Writer Boolector) where
  startSolverProcess feat mbIOh sym = do
    timeout <- SolverGoalTimeout <$>
               (getOpt =<< getOptionSetting boolectorTimeout (getConfiguration sym))
    SMT2.startSolver Boolector SMT2.smtAckResult
                            setInteractiveLogicAndOptions
                            timeout
                            feat
                            (Just boolectorStrictParsing) mbIOh sym
  shutdownSolverProcess = SMT2.shutdownSolver Boolector
