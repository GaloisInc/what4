------------------------------------------------------------------------
-- |
-- Module           : What4.Solver.Boolector
-- Description      : Interface for running Boolector
-- Copyright        : (c) Galois, Inc 2014
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
  , boolectorOptions
  , boolectorAdapter
  , runBoolectorInOverride
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Concurrent
import           Control.Lens(folded)
import           Control.Monad
import           Control.Monad.Identity
import           Data.Bits ( (.|.) )
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString.UTF8 as UTF8
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Parameterized.Some ( Some(..) )
import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import           Numeric.Natural
import           System.Exit
import qualified System.IO.Streams as Streams
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen as PP

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
import           What4.Protocol.SMTWriter
  (smtExprGroundEvalFn, SMTEvalFunctions(..), nullAcknowledgementAction, supportedFeatures)
import           What4.Utils.Process
import           What4.Utils.Streams
import           What4.Utils.HandleReader

data Boolector = Boolector deriving Show

-- | Path to boolector
boolectorPath :: ConfigOption (BaseStringType Unicode)
boolectorPath = configOption knownRepr "boolector_path"

boolectorOptions :: [ConfigDesc]
boolectorOptions =
  [ mkOpt
      boolectorPath
      executablePathOptSty
      (Just (PP.text "Path to boolector executable"))
      (Just (ConcreteString "boolector"))
  ]

boolectorAdapter :: SolverAdapter st
boolectorAdapter =
  SolverAdapter
  { solver_adapter_name = "boolector"
  , solver_adapter_config_options = boolectorOptions
  , solver_adapter_check_sat = \sym logData p cont -> do
      res <- runBoolectorInOverride sym logData p
      cont . runIdentity . traverseSatResult (\x -> pure (x,Nothing)) pure $ res
  , solver_adapter_write_smt2 =
      SMT2.writeDefaultSMT2 () "Boolector" defaultWriteSMTLIB2Features
  }

instance SMT2.SMTLib2Tweaks Boolector where
  smtlib2tweaks = Boolector

runBoolectorInOverride :: ExprBuilder t st
                       -> LogData
                       -> [BoolExpr t]
                       -> IO (SatResult (GroundEvalFn t) ())
runBoolectorInOverride sym logData ps = do
  -- Get boolector path.
  path <- findSolverPath boolectorPath (getConfiguration sym)
  p <- andAllOf sym folded ps

  logSolverEvent sym
    SolverStartSATQuery
    { satQuerySolverName = "Boolector"
    , satQueryReason = logReason logData
    }
  withProcessHandles path ["-m"] Nothing $ \(in_h, out_h, err_h, ph) -> do
      -- Log stderr to output.
      err_stream <- Streams.handleToInputStream err_h
      void $ forkIO $ logErrorStream err_stream (logCallbackVerbose logData 2)
      -- Write SMT2 input to Boolector.
      bindings <- getSymbolVarBimap sym

      in_str  <-
        case logHandle logData of
          Nothing -> Streams.encodeUtf8 =<< Streams.handleToOutputStream in_h
          Just aux_h ->
            do aux_str <- Streams.handleToOutputStream aux_h
               Streams.encodeUtf8 =<< teeOutputStream aux_str =<< Streams.handleToOutputStream in_h

      wtr <- SMT2.newWriter Boolector in_str nullAcknowledgementAction "Boolector"
               False noFeatures False bindings
      SMT2.setLogic wtr SMT2.qf_bv
      SMT2.assume wtr p

      SMT2.writeCheckSat wtr
      SMT2.writeExit wtr
      -- Close input handle to tell boolector input is done.
      Streams.write Nothing in_str

      -- Read stdout to get output.
      out_stream <- Streams.handleToInputStream out_h
      line_stream <- Streams.map UTF8.toString =<< Streams.lines out_stream
      out_lines <- Streams.toList line_stream
      -- Check error code.
      ec <- waitForProcess ph
      case ec of
        ExitSuccess -> return ()
        ExitFailure 10 -> return () -- SAT exit
        ExitFailure 20 -> return () -- UNSAT exit
        ExitFailure exit_code  ->
          fail $ "boolector exited with unexpected code: " ++ show exit_code
      -- Parse output.
      res <- parseBoolectorOutput wtr out_lines
      logSolverEvent sym
         SolverEndSATQuery
         { satQueryResult = forgetModelAndCore res
         , satQueryError  = Nothing
         }
      return res

parseBoolectorOutputLine :: MonadFail m => String -> m (Text, String)
parseBoolectorOutputLine s =
  case words s of
    [nm,v] -> return (Text.pack nm,v)
    _ -> fail $ "Could not parse Boolector output:\n  " ++ show s

boolectorBoolValue :: MonadFail m => String -> m Bool
boolectorBoolValue "1" = return True
boolectorBoolValue "0" = return False
boolectorBoolValue s = fail $ "Could not parse " ++ s ++ " as a Boolean."

boolectorBVValue :: forall m w . MonadFail m => NatRepr w -> String -> m (BV.BV w)
boolectorBVValue w0 s0 = do
  (wNatural, x) <- go 0 0 s0
  Some w <- return $ mkNatRepr wNatural
  case w0 `testEquality` w of
    Just Refl -> return $ BV.mkBV w0 x
    Nothing -> fail "Unexpected number of bits in output."
  where go :: Natural -> Integer -> String -> m (Natural, Integer)
        go w r [] = return (w, r)
        go w r ('1':s) = go (w+1) (2 * r + 1) s
        go w r ('0':s) = go (w+1) (2 * r) s
        go _ _ _ = fail $ "Could not parse " ++ s0 ++ " as a bitvector."

lookupBoolectorVar :: MonadFail m
                   => Map Text String
                      -- ^ Map from variable names to value
                   -> (String -> m r)
                      -- ^ Function for interpreting value
                   -> Text
                      -- ^ Name of variable to lookup
                   -> m r
lookupBoolectorVar m evalFn nm =
  case Map.lookup nm m of
    Just r -> evalFn r
    Nothing -> fail $ "Could not find variable "
                   ++ Text.unpack nm ++ " in Boolector output."

parseBoolectorOutput :: SMT2.WriterConn t (SMT2.Writer Boolector)
                     -> [String]
                     -> IO (SatResult (GroundEvalFn t) ())
parseBoolectorOutput c out_lines =
  case out_lines of
    "unsat":_ -> return (Unsat ())
    "sat":mdl_lines0 -> do
      let mdl_lines = filter (/= "") mdl_lines0
      m <- Map.fromList <$> mapM parseBoolectorOutputLine mdl_lines
      let evalBool tm = lookupBoolectorVar m boolectorBoolValue   $ Builder.toLazyText $ SMT2.renderTerm tm
      let evalBV :: NatRepr w -> SMT2.Term -> IO (BV.BV w)
          evalBV w tm = lookupBoolectorVar m (boolectorBVValue w) $ Builder.toLazyText $ SMT2.renderTerm tm
      let evalReal _ = fail "Boolector does not support real variables."
      let evalFloat _ _ = fail "Boolector does not support floats."
      let evalStr _ = fail "Boolector does not support strings."
      let evalFns = SMTEvalFunctions { smtEvalBool = evalBool
                                     , smtEvalBV = evalBV
                                     , smtEvalReal = evalReal
                                     , smtEvalFloat = evalFloat
                                     , smtEvalBvArray = Nothing
                                     , smtEvalString = evalStr
                                     }
      Sat <$> smtExprGroundEvalFn c evalFns
    [] -> fail "Boolector returned no output."
    h:_ -> fail $ "Could not parse boolector output: " ++ h

boolectorFeatures :: ProblemFeatures
boolectorFeatures = useSymbolicArrays
                .|. useBitvectors

instance SMT2.SMTLib2GenericSolver Boolector where
  defaultSolverPath _ = findSolverPath boolectorPath . getConfiguration
  defaultSolverArgs _ _ = return ["--smt2", "--smt2-model", "--incremental", "--output-format=smt2"]
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
    when (supportedFeatures writer `hasProblemFeature` useUnsatCores) $ do
      SMT2.setOption writer "produce-unsat-cores" "true"
    SMT2.setLogic writer SMT2.allSupported

instance OnlineSolver (SMT2.Writer Boolector) where
  startSolverProcess = SMT2.startSolver Boolector SMT2.smtAckResult setInteractiveLogicAndOptions
  shutdownSolverProcess = SMT2.shutdownSolver Boolector
