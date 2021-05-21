------------------------------------------------------------------------
-- |
-- Module           : What4.Solver.Bitwuzla
-- Description      : Interface for running Bitwuzla
-- Copyright        : (c) Galois, Inc 2014-2023
-- License          : BSD3
-- Maintainer       : Ryan Scott <rscott@galois.com>
-- Stability        : provisional
--
-- This module provides an interface for running Bitwuzla and parsing
-- the results back.
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
module What4.Solver.Bitwuzla
  ( Bitwuzla(..)
  , bitwuzlaPath
  , bitwuzlaTimeout
  , bitwuzlaOptions
  , bitwuzlaAdapter
  , runBitwuzlaInOverride
  , withBitwuzla
  , bitwuzlaFeatures
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
import qualified What4.Protocol.SMTLib2.Syntax as Syntax
import           What4.Protocol.SMTLib2.Response ( strictSMTParseOpt )
import           What4.SatResult
import           What4.Solver.Adapter
import           What4.Utils.Process

data Bitwuzla = Bitwuzla deriving Show

-- | Path to bitwuzla
bitwuzlaPath :: ConfigOption (BaseStringType Unicode)
bitwuzlaPath = configOption knownRepr "solver.bitwuzla.path"

-- | Per-check timeout, in milliseconds (zero is none)
bitwuzlaTimeout :: ConfigOption BaseIntegerType
bitwuzlaTimeout = configOption knownRepr "solver.bitwuzla.timeout"

-- | Control strict parsing for Bitwuzla solver responses (defaults
-- to solver.strict-parsing option setting).
bitwuzlaStrictParsing :: ConfigOption BaseBoolType
bitwuzlaStrictParsing = configOption knownRepr "solver.bitwuzla.strict_parsing"

bitwuzlaOptions :: [ConfigDesc]
bitwuzlaOptions =
  let bpOpt co = mkOpt
                 co
                 executablePathOptSty
                 (Just "Path to bitwuzla executable")
                 (Just (ConcreteString "bitwuzla"))
      mkTmo co = mkOpt co
                 integerOptSty
                 (Just "Per-check timeout in milliseconds (zero is none)")
                 (Just (ConcreteInteger 0))
      bp = bpOpt bitwuzlaPath
  in [ bp
     , mkTmo bitwuzlaTimeout
     , copyOpt (const $ configOptionText bitwuzlaStrictParsing) strictSMTParseOpt
     ] <> SMT2.smtlib2Options

bitwuzlaAdapter :: SolverAdapter st
bitwuzlaAdapter =
  SolverAdapter
  { solver_adapter_name = "bitwuzla"
  , solver_adapter_config_options = bitwuzlaOptions
  , solver_adapter_check_sat = runBitwuzlaInOverride
  , solver_adapter_write_smt2 =
      SMT2.writeDefaultSMT2 () "Bitwuzla" defaultWriteSMTLIB2Features
      (Just bitwuzlaStrictParsing)
  }

instance SMT2.SMTLib2Tweaks Bitwuzla where
  smtlib2tweaks = Bitwuzla

runBitwuzlaInOverride
  :: ExprBuilder t st fs
  -> LogData
  -> [BoolExpr t]
  -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
  -> IO a
runBitwuzlaInOverride =
  SMT2.runSolverInOverride Bitwuzla SMT2.nullAcknowledgementAction
  bitwuzlaFeatures (Just bitwuzlaStrictParsing)

-- | Run Bitwuzla in a session. Bitwuzla will be configured to produce models, but
-- otherwise left with the default configuration.
withBitwuzla
  :: ExprBuilder t st fs
  -> FilePath
    -- ^ Path to Bitwuzla executable
  -> LogData
  -> (SMT2.Session t Bitwuzla -> IO a)
    -- ^ Action to run
  -> IO a
withBitwuzla = SMT2.withSolver Bitwuzla SMT2.nullAcknowledgementAction
               bitwuzlaFeatures (Just bitwuzlaStrictParsing)

bitwuzlaFeatures :: ProblemFeatures
bitwuzlaFeatures = useBitvectors
               .|. useFloatingPoint
               .|. useQuantifiers
               .|. useSymbolicArrays
               .|. useUninterpFunctions
               .|. useUnsatCores
               .|. useUnsatAssumptions

instance SMT2.SMTLib2GenericSolver Bitwuzla where
  defaultSolverPath _ = findSolverPath bitwuzlaPath . getConfiguration
  defaultSolverArgs _ sym = do
    let cfg = getConfiguration sym
    timeout <- getOption =<< getOptionSetting bitwuzlaTimeout cfg
    let extraOpts = case timeout of
                      Just (ConcreteInteger n) | n > 0 -> ["-t", show n]
                      _ -> []
    return $ ["--lang", "smt2"] ++ extraOpts
  defaultFeatures _ = bitwuzlaFeatures
  setDefaultLogicAndOptions writer = do
    SMT2.setLogic writer Syntax.allLogic
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
    SMT2.setLogic writer Syntax.allLogic

instance OnlineSolver (SMT2.Writer Bitwuzla) where
  startSolverProcess feat mbIOh sym = do
    timeout <- SolverGoalTimeout <$>
               (getOpt =<< getOptionSetting bitwuzlaTimeout (getConfiguration sym))
    SMT2.startSolver Bitwuzla SMT2.smtAckResult
                            setInteractiveLogicAndOptions
                            timeout
                            feat
                            (Just bitwuzlaStrictParsing) mbIOh sym
  shutdownSolverProcess = SMT2.shutdownSolver Bitwuzla
