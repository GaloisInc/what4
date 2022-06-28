------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.CVC4
-- Description : Solver adapter code for CVC4
-- Copyright   : (c) Galois, Inc 2015-2020
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- CVC4-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module What4.Solver.CVC4
  ( CVC4(..)
  , cvc4Features
  , cvc4Adapter
  , cvc4Path
  , cvc4Timeout
  , cvc4Options
  , runCVC4InOverride
  , withCVC4
  , writeCVC4SMT2File
  , writeMultiAsmpCVC4SMT2File
  ) where

import           Control.Monad (forM_, when)
import           Data.Bits
import           Data.String
import           System.IO
import qualified System.IO.Streams as Streams

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
import qualified What4.Protocol.SMTLib2.Response as RSP
import qualified What4.Protocol.SMTLib2.Syntax as Syntax
import           What4.Protocol.SMTWriter
import           What4.SatResult
import           What4.Solver.Adapter
import           What4.Utils.Process


intWithRangeOpt :: ConfigOption BaseIntegerType -> Integer -> Integer -> ConfigDesc
intWithRangeOpt nm lo hi = mkOpt nm sty Nothing Nothing
  where sty = integerWithRangeOptSty (Inclusive lo) (Inclusive hi)

data CVC4 = CVC4 deriving Show

-- | Path to cvc4
cvc4Path :: ConfigOption (BaseStringType Unicode)
cvc4Path = configOption knownRepr "solver.cvc4.path"

cvc4PathOLD :: ConfigOption (BaseStringType Unicode)
cvc4PathOLD = configOption knownRepr "cvc4_path"

cvc4RandomSeed :: ConfigOption BaseIntegerType
cvc4RandomSeed = configOption knownRepr "solver.cvc4.random-seed"

cvc4RandomSeedOLD :: ConfigOption BaseIntegerType
cvc4RandomSeedOLD = configOption knownRepr "cvc4.random-seed"

-- | Per-check timeout, in milliseconds (zero is none)
cvc4Timeout :: ConfigOption BaseIntegerType
cvc4Timeout = configOption knownRepr "solver.cvc4.timeout"

cvc4TimeoutOLD :: ConfigOption BaseIntegerType
cvc4TimeoutOLD = configOption knownRepr "cvc4_timeout"

-- | Control strict parsing for Boolector solver responses (defaults
-- to solver.strict-parsing option setting).
cvc4StrictParsing :: ConfigOption BaseBoolType
cvc4StrictParsing = configOption knownRepr "solver.cvc4.strict_parsing"

cvc4Options :: [ConfigDesc]
cvc4Options =
  let pathOpt co = mkOpt co
                   executablePathOptSty
                   (Just "Path to CVC4 executable")
                   (Just (ConcreteString "cvc4"))
      p1 = pathOpt cvc4Path
      r1 = intWithRangeOpt cvc4RandomSeed (negate (2^(30::Int)-1)) (2^(30::Int)-1)
      tmOpt co = mkOpt co
                 integerOptSty
                 (Just "Per-check timeout in milliseconds (zero is none)")
                 (Just (ConcreteInteger 0))
      t1 = tmOpt cvc4Timeout
  in [ p1, r1, t1
     , copyOpt (const $ configOptionText cvc4StrictParsing) strictSMTParseOpt
     , deprecatedOpt [p1] $ pathOpt cvc4PathOLD
     , deprecatedOpt [r1] $ intWithRangeOpt cvc4RandomSeedOLD
       (negate (2^(30::Int)-1)) (2^(30::Int)-1)
     , deprecatedOpt [t1] $ tmOpt cvc4TimeoutOLD
     ] <> SMT2.smtlib2Options

cvc4Adapter :: SolverAdapter st
cvc4Adapter =
  SolverAdapter
  { solver_adapter_name = "cvc4"
  , solver_adapter_config_options = cvc4Options
  , solver_adapter_check_sat = runCVC4InOverride
  , solver_adapter_write_smt2 = writeCVC4SMT2File
  }

indexType :: [SMT2.Sort] -> SMT2.Sort
indexType [i] = i
indexType il = SMT2.smtlib2StructSort @CVC4 il

indexCtor :: [SMT2.Term] -> SMT2.Term
indexCtor [i] = i
indexCtor il = SMT2.smtlib2StructCtor @CVC4 il

instance SMT2.SMTLib2Tweaks CVC4 where
  smtlib2tweaks = CVC4

  smtlib2arrayType il r = SMT2.arraySort (indexType il) r

  smtlib2arrayConstant = Just $ \idx rtp v ->
    SMT2.arrayConst (indexType idx) rtp v
  smtlib2arraySelect a i = SMT2.arraySelect a (indexCtor i)
  smtlib2arrayUpdate a i = SMT2.arrayStore a (indexCtor i)

  smtlib2declareStructCmd _ = Nothing
  smtlib2StructSort []  = Syntax.varSort "Tuple"
  smtlib2StructSort tps = Syntax.Sort $ "(Tuple" <> foldMap f tps <> ")"
    where f x = " " <> Syntax.unSort x

  smtlib2StructCtor args = Syntax.term_app "mkTuple" args
  smtlib2StructProj _n i x = Syntax.term_app (Syntax.builder_list ["_", "tupSel", fromString (show i)]) [ x ]

cvc4Features :: ProblemFeatures
cvc4Features = useComputableReals
           .|. useIntegerArithmetic
           .|. useSymbolicArrays
           .|. useStrings
           .|. useStructs
           .|. useFloatingPoint
           .|. useBitvectors
           .|. useQuantifiers

writeMultiAsmpCVC4SMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeMultiAsmpCVC4SMT2File sym h ps = do
  bindings <- getSymbolVarBimap sym
  out_str  <- Streams.encodeUtf8 =<< Streams.handleToOutputStream h
  in_str <- Streams.nullInput
  let cfg = getConfiguration sym
  strictness <- maybe Strict
                (\c -> if fromConcreteBool c then Strict else Lenient) <$>
                (getOption =<< getOptionSetting RSP.strictSMTParsing cfg)
  c <- SMT2.newWriter CVC4 out_str in_str nullAcknowledgementAction strictness "CVC4"
         True cvc4Features True bindings
  SMT2.setLogic c Syntax.allLogic
  SMT2.setProduceModels c True
  forM_ ps $ SMT2.assume c
  SMT2.writeCheckSat c
  SMT2.writeExit c

writeCVC4SMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeCVC4SMT2File sym h ps = writeMultiAsmpCVC4SMT2File sym h ps

instance SMT2.SMTLib2GenericSolver CVC4 where
  defaultSolverPath _ = findSolverPath cvc4Path . getConfiguration

  defaultSolverArgs _ sym = do
    let cfg = getConfiguration sym
    timeout <- getOption =<< getOptionSetting cvc4Timeout cfg
    let extraOpts = case timeout of
                      Just (ConcreteInteger n) | n > 0 -> ["--tlimit-per=" ++ show n]
                      _ -> []
    return $ ["--lang", "smt2", "--incremental", "--strings-exp", "--fp-exp"] ++ extraOpts

  getErrorBehavior _ = SMT2.queryErrorBehavior

  defaultFeatures _ = cvc4Features

  supportsResetAssertions _ = True

  setDefaultLogicAndOptions writer = do
    -- Tell CVC4 to use all supported logics.
    SMT2.setLogic writer Syntax.allLogic
    -- Tell CVC4 to produce models
    SMT2.setProduceModels writer True

runCVC4InOverride
  :: ExprBuilder t st fs
  -> LogData
  -> [BoolExpr t]
  -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
  -> IO a
runCVC4InOverride = SMT2.runSolverInOverride CVC4 nullAcknowledgementAction
                    (SMT2.defaultFeatures CVC4) (Just cvc4StrictParsing)

-- | Run CVC4 in a session. CVC4 will be configured to produce models, but
-- otherwise left with the default configuration.
withCVC4
  :: ExprBuilder t st fs
  -> FilePath
    -- ^ Path to CVC4 executable
  -> LogData
  -> (SMT2.Session t CVC4 -> IO a)
    -- ^ Action to run
  -> IO a
withCVC4 = SMT2.withSolver CVC4 nullAcknowledgementAction
           (SMT2.defaultFeatures CVC4) (Just cvc4StrictParsing)

setInteractiveLogicAndOptions ::
  SMT2.SMTLib2Tweaks a =>
  WriterConn t (SMT2.Writer a) ->
  IO ()
setInteractiveLogicAndOptions writer = do
    -- Tell CVC4 to acknowledge successful commands
    SMT2.setOption writer "print-success"  "true"
    -- Tell CVC4 to produce models
    SMT2.setOption writer "produce-models" "true"
    -- Tell CVC4 to make declarations global, so they are not removed by 'pop' commands
    SMT2.setOption writer "global-declarations" "true"
    -- Tell CVC4 to compute UNSAT cores, if that feature is enabled
    when (supportedFeatures writer `hasProblemFeature` useUnsatCores) $ do
      SMT2.setOption writer "produce-unsat-cores" "true"
    -- Tell CVC4 to use all supported logics.
    SMT2.setLogic writer Syntax.allLogic

instance OnlineSolver (SMT2.Writer CVC4) where
  startSolverProcess feat mbIOh sym = do
    timeout <- SolverGoalTimeout <$>
               (getOpt =<< getOptionSetting cvc4Timeout (getConfiguration sym))
    SMT2.startSolver CVC4 SMT2.smtAckResult setInteractiveLogicAndOptions
          timeout feat (Just cvc4StrictParsing) mbIOh sym

  shutdownSolverProcess = SMT2.shutdownSolver CVC4
