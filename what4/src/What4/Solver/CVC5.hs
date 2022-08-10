------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.CVC5
-- Description : Solver adapter code for cvc5
-- Copyright   : (c) Galois, Inc 2022
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- CVC5-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module What4.Solver.CVC5
  ( CVC5(..)
  , cvc5Features
  , cvc5Adapter
  , cvc5Path
  , cvc5Timeout
  , cvc5Options
  , runCVC5InOverride
  , withCVC5
  , writeCVC5SMT2File
  , writeMultiAsmpCVC5SMT2File
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

data CVC5 = CVC5 deriving Show

-- | Path to cvc5
cvc5Path :: ConfigOption (BaseStringType Unicode)
cvc5Path = configOption knownRepr "solver.cvc5.path"

cvc5RandomSeed :: ConfigOption BaseIntegerType
cvc5RandomSeed = configOption knownRepr "solver.cvc5.random-seed"

-- | Per-check timeout, in milliseconds (zero is none)
cvc5Timeout :: ConfigOption BaseIntegerType
cvc5Timeout = configOption knownRepr "solver.cvc5.timeout"

-- | Control strict parsing for cvc5 solver responses (defaults
-- to solver.strict-parsing option setting).
cvc5StrictParsing :: ConfigOption BaseBoolType
cvc5StrictParsing = configOption knownRepr "solver.cvc5.strict_parsing"

cvc5Options :: [ConfigDesc]
cvc5Options =
  let pathOpt co = mkOpt co
                   executablePathOptSty
                   (Just "Path to CVC5 executable")
                   (Just (ConcreteString "cvc5"))
      p1 = pathOpt cvc5Path
      r1 = intWithRangeOpt cvc5RandomSeed (negate (2^(30::Int)-1)) (2^(30::Int)-1)
      tmOpt co = mkOpt co
                 integerOptSty
                 (Just "Per-check timeout in milliseconds (zero is none)")
                 (Just (ConcreteInteger 0))
      t1 = tmOpt cvc5Timeout
  in [ p1, r1, t1
     , copyOpt (const $ configOptionText cvc5StrictParsing) strictSMTParseOpt
     ] <> SMT2.smtlib2Options

cvc5Adapter :: SolverAdapter st
cvc5Adapter =
  SolverAdapter
  { solver_adapter_name = "cvc5"
  , solver_adapter_config_options = cvc5Options
  , solver_adapter_check_sat = runCVC5InOverride
  , solver_adapter_write_smt2 = writeCVC5SMT2File
  }

indexType :: [SMT2.Sort] -> SMT2.Sort
indexType [i] = i
indexType il = SMT2.smtlib2StructSort @CVC5 il

indexCtor :: [SMT2.Term] -> SMT2.Term
indexCtor [i] = i
indexCtor il = SMT2.smtlib2StructCtor @CVC5 il

instance SMT2.SMTLib2Tweaks CVC5 where
  smtlib2tweaks = CVC5

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

cvc5Features :: ProblemFeatures
cvc5Features = useComputableReals
           .|. useIntegerArithmetic
           .|. useSymbolicArrays
           .|. useStrings
           .|. useStructs
           .|. useFloatingPoint
           .|. useUnsatCores
           .|. useUnsatAssumptions
           .|. useUninterpFunctions
           .|. useDefinedFunctions
           .|. useBitvectors
           .|. useQuantifiers
           .|. useProduceAbducts

writeMultiAsmpCVC5SMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeMultiAsmpCVC5SMT2File sym h ps = do
  bindings <- getSymbolVarBimap sym
  out_str  <- Streams.encodeUtf8 =<< Streams.handleToOutputStream h
  in_str <- Streams.nullInput
  let cfg = getConfiguration sym
  strictness <- maybe Strict
                (\c -> if fromConcreteBool c then Strict else Lenient) <$>
                (getOption =<< getOptionSetting RSP.strictSMTParsing cfg)
  c <- SMT2.newWriter CVC5 out_str in_str nullAcknowledgementAction strictness "CVC5"
         True cvc5Features True bindings
  SMT2.setLogic c Syntax.allLogic
  SMT2.setProduceModels c True
  forM_ ps $ SMT2.assume c
  SMT2.writeCheckSat c
  SMT2.writeExit c

writeCVC5SMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeCVC5SMT2File sym h ps = writeMultiAsmpCVC5SMT2File sym h ps

instance SMT2.SMTLib2GenericSolver CVC5 where
  defaultSolverPath _ = findSolverPath cvc5Path . getConfiguration

  defaultSolverArgs _ sym = do
    let cfg = getConfiguration sym
    timeout <- getOption =<< getOptionSetting cvc5Timeout cfg
    let extraOpts = case timeout of
                      Just (ConcreteInteger n) | n > 0 -> ["--tlimit-per=" ++ show n]
                      _ -> []
    return $ ["--lang", "smt2", "--incremental", "--strings-exp", "--fp-exp"] ++ extraOpts

  getErrorBehavior _ = SMT2.queryErrorBehavior

  defaultFeatures _ = cvc5Features

  supportsResetAssertions _ = True

  setDefaultLogicAndOptions writer = do
    -- Tell cvc5 to use all supported logics.
    SMT2.setLogic writer Syntax.allLogic
    -- Tell cvc5 to produce models
    SMT2.setProduceModels writer True
    -- Tell cvc5 to produce abducts
    SMT2.setOption writer "produce-abducts" "true"

runCVC5InOverride
  :: ExprBuilder t st fs
  -> LogData
  -> [BoolExpr t]
  -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
  -> IO a
runCVC5InOverride = SMT2.runSolverInOverride CVC5 nullAcknowledgementAction
                    (SMT2.defaultFeatures CVC5) (Just cvc5StrictParsing)

-- | Run cvc5 in a session. cvc5 will be configured to produce models, but
-- otherwise left with the default configuration.
withCVC5
  :: ExprBuilder t st fs
  -> FilePath
    -- ^ Path to cvc5 executable
  -> LogData
  -> (SMT2.Session t CVC5 -> IO a)
    -- ^ Action to run
  -> IO a
withCVC5 = SMT2.withSolver CVC5 nullAcknowledgementAction
           (SMT2.defaultFeatures CVC5) (Just cvc5StrictParsing)

setInteractiveLogicAndOptions ::
  SMT2.SMTLib2Tweaks a =>
  WriterConn t (SMT2.Writer a) ->
  IO ()
setInteractiveLogicAndOptions writer = do
    -- Tell cvc5 to acknowledge successful commands
    SMT2.setOption writer "print-success"  "true"
    -- Tell cvc5 to produce models
    SMT2.setOption writer "produce-models" "true"
    -- Tell cvc5 to make declarations global, so they are not removed by 'pop' commands
    SMT2.setOption writer "global-declarations" "true"
    -- Tell cvc5 to compute UNSAT cores, if that feature is enabled
    when (supportedFeatures writer `hasProblemFeature` useUnsatCores) $ do
      SMT2.setOption writer "produce-unsat-cores" "true"
    -- Tell cvc5 to produce abducts, if that feature is enabled
    when (supportedFeatures writer `hasProblemFeature` useProduceAbducts) $ do
      SMT2.setOption writer "produce-abducts" "true"
    -- Tell cvc5 to use all supported logics.
    SMT2.setLogic writer Syntax.allLogic

instance OnlineSolver (SMT2.Writer CVC5) where
  startSolverProcess feat mbIOh sym = do
    timeout <- SolverGoalTimeout <$>
               (getOpt =<< getOptionSetting cvc5Timeout (getConfiguration sym))
    SMT2.startSolver CVC5 SMT2.smtAckResult setInteractiveLogicAndOptions
          timeout feat (Just cvc5StrictParsing) mbIOh sym

  shutdownSolverProcess = SMT2.shutdownSolver CVC5
