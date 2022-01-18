------------------------------------------------------------------------
-- |
-- Module           : What4.Solver.Bitwuzla
-- Description      : Interface for running Bitwuzla
-- Copyright        : (c) Galois, Inc 2014-2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an interface for running Bitwuzla and parsing
-- the results back.
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module What4.Solver.Bitwuzla
  ( Bitwuzla(..)
  , bitwuzlaPath
  , bitwuzlaTimeout
  , bitwuzlaOptions
  , bitwuzlaAdapter
  , bitwuzlaFeatures
  , runBitwuzlaInOverride
  ) where

import           Control.Monad ( when )
import           Data.Bits ( (.|.) )

import qualified What4.BaseTypes as WT
import qualified What4.Concrete as Concrete
import qualified What4.Config as Config
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import qualified What4.Interface as WI
import qualified What4.ProblemFeatures as Features
import qualified What4.Protocol.Online as Online
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Protocol.SMTLib2.Response as SMT2
import qualified What4.SatResult as SatResult
import qualified What4.Solver.Adapter as Adapter
import qualified What4.Utils.Process as Process

data Bitwuzla = Bitwuzla deriving Show

-- | Path to bitwuzla
bitwuzlaPath :: Config.ConfigOption (WT.BaseStringType WT.Unicode)
bitwuzlaPath = Config.configOption WT.knownRepr "solver.bitwuzla.path"

-- | Per-check timeout, in milliseconds (zero is none)
bitwuzlaTimeout :: Config.ConfigOption WI.BaseIntegerType
bitwuzlaTimeout = Config.configOption WI.knownRepr "solver.bitwuzla.timeout"

-- | Control strict parsing for Bitwuzla solver responses (defaults
-- to solver.strict-parsing option setting).
bitwuzlaStrictParsing :: Config.ConfigOption WI.BaseBoolType
bitwuzlaStrictParsing = Config.configOption WI.knownRepr "solver.bitwuzla.strict_parsing"

bitwuzlaOptions :: [Config.ConfigDesc]
bitwuzlaOptions =
  let bpopt co = Config.mkOpt co
                              Config.executablePathOptSty
                              (Just "Path to bitwuzla executable")
                              (Just (Concrete.ConcreteString "bitwuzla"))
      mkTmo co = Config.mkOpt co
                              Config.integerOptSty
                              (Just "Per-check timeout in milliseconds (zero is none)")
                              (Just (Concrete.ConcreteInteger 0))
      bp = bpopt bitwuzlaPath
  in [ bp
     , mkTmo bitwuzlaTimeout
     , Config.copyOpt (const $ Config.configOptionText bitwuzlaStrictParsing) SMT2.strictSMTParseOpt
     ] <> SMT2.smtlib2Options

bitwuzlaAdapter :: Adapter.SolverAdapter st
bitwuzlaAdapter = Adapter.SolverAdapter
  { Adapter.solver_adapter_name = "bitwuzla"
  , Adapter.solver_adapter_config_options = bitwuzlaOptions
  , Adapter.solver_adapter_check_sat = runBitwuzlaInOverride
  , Adapter.solver_adapter_write_smt2 =
    SMT2.writeDefaultSMT2 () "Bitwuzla" Adapter.defaultWriteSMTLIB2Features
    (Just bitwuzlaStrictParsing)
  }

bitwuzlaFeatures :: Features.ProblemFeatures
bitwuzlaFeatures = Features.useSymbolicArrays
               .|. Features.useBitvectors
               .|. Features.useFloatingPoint

instance SMT2.SMTLib2Tweaks Bitwuzla where
  smtlib2tweaks = Bitwuzla

runBitwuzlaInOverride
  :: ExprBuilder t st fs
  -> Adapter.LogData
  -> [BoolExpr t]
  -> (SatResult.SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
  -> IO a
runBitwuzlaInOverride =
  SMT2.runSolverInOverride Bitwuzla SMT2.nullAcknowledgementAction
     bitwuzlaFeatures (Just bitwuzlaStrictParsing)

instance SMT2.SMTLib2GenericSolver Bitwuzla where
  defaultSolverPath _ = Process.findSolverPath bitwuzlaPath . WI.getConfiguration
  defaultSolverArgs _ _ = return ["--smt2", "--incremental", "--output-format=smt2", "-e=0"]
  defaultFeatures _ = bitwuzlaFeatures
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
    when (SMT2.supportedFeatures writer `Features.hasProblemFeature` Features.useUnsatCores) $ do
      SMT2.setOption writer "produce-unsat-cores" "true"
    SMT2.setLogic writer SMT2.allSupported

instance Online.OnlineSolver (SMT2.Writer Bitwuzla) where
  startSolverProcess feat mbIOh sym = do
    timeout <- Online.SolverGoalTimeout <$>
                 (Config.getOpt =<< Config.getOptionSetting bitwuzlaTimeout (WI.getConfiguration sym))
    SMT2.startSolver Bitwuzla SMT2.smtAckResult
                            setInteractiveLogicAndOptions
                            timeout
                            feat
                            (Just bitwuzlaStrictParsing) mbIOh sym
  shutdownSolverProcess = SMT2.shutdownSolver Bitwuzla
