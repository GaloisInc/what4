------------------------------------------------------------------------
-- |
-- module           : What4.Solver.DReal
-- Description      : Interface for running dReal
-- Copyright        : (c) Galois, Inc 2014-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an interface for running dReal and parsing
-- the results back.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
module What4.Solver.DReal
  ( DReal(..)
  , DRealBindings
  , ExprRangeBindings
  , getAvgBindings
  , getBoundBindings
  , drealPath
  , drealOptions
  , drealAdapter
  , writeDRealSMT2File
  , runDRealInOverride
  ) where

import           Control.Concurrent
import           Control.Exception
import           Control.Lens(folded)
import           Control.Monad
import           Data.Attoparsec.ByteString.Char8 hiding (try)
import qualified Data.ByteString.UTF8 as UTF8
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text.Encoding ( decodeUtf8 )
import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import           Numeric
import           System.Exit
import           System.IO
import           System.IO.Error
import qualified System.IO.Streams as Streams
import qualified System.IO.Streams.Attoparsec as Streams
import           System.Process

import           What4.BaseTypes
import           What4.Config
import           What4.Solver.Adapter
import           What4.Concrete
import           What4.Interface
import           What4.ProblemFeatures
import           What4.SatResult
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Protocol.SMTLib2.Response as RSP
import qualified What4.Protocol.SMTWriter as SMTWriter
import           What4.Utils.Process
import           What4.Utils.Streams (logErrorStream)
import           What4.Utils.HandleReader

data DReal = DReal deriving Show

-- | Path to dReal
drealPath :: ConfigOption (BaseStringType Unicode)
drealPath = configOption knownRepr "solver.dreal.path"

drealPathOLD :: ConfigOption (BaseStringType Unicode)
drealPathOLD = configOption knownRepr "dreal_path"

drealOptions :: [ConfigDesc]
drealOptions =
  let dpOpt co = mkOpt co
                 executablePathOptSty
                 (Just "Path to dReal executable")
                 (Just (ConcreteString "dreal"))
      dp = dpOpt drealPath
  in [ dp
     , deprecatedOpt [dp] $ dpOpt drealPathOLD
     ] <> SMT2.smtlib2Options

drealAdapter :: SolverAdapter st
drealAdapter =
  SolverAdapter
  { solver_adapter_name = "dreal"
  , solver_adapter_config_options = drealOptions
  , solver_adapter_check_sat = \sym logData ps cont ->
      runDRealInOverride sym logData ps $ \res ->
         case res of
           Sat (c,m) -> do
             evalFn <- getAvgBindings c m
             rangeFn <- getBoundBindings c m
             cont (Sat (evalFn, Just rangeFn))
           Unsat x -> cont (Unsat x)
           Unknown -> cont Unknown

  , solver_adapter_write_smt2 = writeDRealSMT2File
  , solver_adapter_with_online_solver = \_ _ _ -> fail "dReal does not support online solving"
  }

instance SMT2.SMTLib2Tweaks DReal where
  smtlib2tweaks = DReal

writeDRealSMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeDRealSMT2File sym h ps = do
  bindings <- getSymbolVarBimap sym
  out_str <- Streams.encodeUtf8 =<< Streams.handleToOutputStream h
  in_str <- Streams.nullInput
  let cfg = getConfiguration sym
  strictness <- maybe SMTWriter.Strict
                (\c -> if fromConcreteBool c
                       then SMTWriter.Strict
                       else SMTWriter.Lenient) <$>
                (getOption =<< getOptionSetting RSP.strictSMTParsing cfg)
  c <- SMT2.newWriter DReal out_str in_str SMTWriter.nullAcknowledgementAction strictness "dReal"
          False useComputableReals False bindings
  SMT2.setProduceModels c True
  SMT2.setLogic c (SMT2.Logic "QF_NRA")
  forM_ ps (SMT2.assume c)
  SMT2.writeCheckSat c
  SMT2.writeExit c

type DRealBindings = Map Text (Either Bool (Maybe Rational, Maybe Rational))

getAvgBindings :: SMT2.WriterConn t (SMT2.Writer DReal)
               -> DRealBindings
               -> IO (GroundEvalFn t)
getAvgBindings c m = do
  let evalBool tm =
        case Map.lookup (Builder.toLazyText (SMT2.renderTerm tm)) m of
          Just (Right _) -> fail "Expected Boolean variable"
          Just (Left b) -> return b
          Nothing -> return False
      evalBV _ _ = fail "dReal does not support bitvectors."
      evalStr _ = fail "dReal does not support strings."
      evalReal tm = do
        case Map.lookup (Builder.toLazyText (SMT2.renderTerm tm)) m of
          Just (Right vs) -> return (drealAvgBinding vs)
          Just (Left _) -> fail "Expected Real variable"
          Nothing -> return 0
      evalFloat _ _ = fail "dReal does not support floats."
  let evalFns = SMTWriter.SMTEvalFunctions { SMTWriter.smtEvalBool = evalBool
                                           , SMTWriter.smtEvalBV = evalBV
                                           , SMTWriter.smtEvalReal = evalReal
                                           , SMTWriter.smtEvalFloat = evalFloat
                                           , SMTWriter.smtEvalBvArray = Nothing
                                           , SMTWriter.smtEvalString = evalStr
                                           }
  SMTWriter.smtExprGroundEvalFn c evalFns

getMaybeEval :: ((Maybe Rational, Maybe Rational) -> Maybe Rational)
             -> SMT2.WriterConn t (SMT2.Writer DReal)
             -> DRealBindings
             -> IO (RealExpr t -> IO (Maybe Rational))
getMaybeEval proj c m = do
  let evalBool tm =
        case Map.lookup (Builder.toLazyText (SMT2.renderTerm tm)) m of
          Just (Right _) -> fail "expected boolean term"
          Just (Left b) -> return b
          Nothing -> fail "unbound boolean variable"
      evalBV _ _ = fail "dReal does not return Bitvector values."
      evalStr _ = fail "dReal does not return string values."
      evalReal tm = do
        case Map.lookup (Builder.toLazyText (SMT2.renderTerm tm)) m of
          Just (Right v) ->
            case proj v of
              Just x  -> return x
              Nothing -> throwIO (userError "unbound")
          Just (Left _) -> fail "expected real variable"
          Nothing -> throwIO (userError "unbound")
      evalFloat _ _ = fail "dReal does not support floats."
  let evalFns = SMTWriter.SMTEvalFunctions { SMTWriter.smtEvalBool = evalBool
                                           , SMTWriter.smtEvalBV = evalBV
                                           , SMTWriter.smtEvalReal = evalReal
                                           , SMTWriter.smtEvalFloat = evalFloat
                                           , SMTWriter.smtEvalBvArray = Nothing
                                           , SMTWriter.smtEvalString = evalStr
                                           }
  GroundEvalFn evalFn <- SMTWriter.smtExprGroundEvalFn c evalFns
  let handler e | isUserError e
                , ioeGetErrorString e == "unbound" = do
        return Nothing
      handler e = throwIO e
  return $ \elt -> (Just <$> evalFn elt) `catch` handler

getBoundBindings :: SMT2.WriterConn t (SMT2.Writer DReal)
                 -> DRealBindings
                 -> IO (ExprRangeBindings t)
getBoundBindings c m = do
  l_evalFn <- getMaybeEval fst c m
  h_evalFn <- getMaybeEval snd c m
  return $ \e -> (,) <$> l_evalFn e <*> h_evalFn e

drealAvgBinding :: (Maybe Rational, Maybe Rational) -> Rational
drealAvgBinding (Nothing, Nothing) = 0
drealAvgBinding (Nothing, Just r)  = r
drealAvgBinding (Just r, Nothing)  = r
drealAvgBinding (Just r1, Just r2) = (r1+r2)/2

dRealResponse :: Parser (SatResult [(Text, Either Bool (Maybe Rational, Maybe Rational))] ())
dRealResponse =
  msum
  [ do _ <- string "unsat"
       return (Unsat ())

  , do _ <- string "unknown"
       return Unknown

  , do _ <- string "delta-sat"
       _ <- takeTill (\c -> c == '\n' || c == '\r')
       endOfLine
       bs <- many' dRealBinding
       endOfInput
       return (Sat bs)
  ]

dRealBinding :: Parser (Text, Either Bool (Maybe Rational, Maybe Rational))
dRealBinding = do
    skipSpace

    nm <- takeWhile1 (not . isSpace)

    skipSpace
    _ <- char ':'
    skipSpace

    val <- msum
      [ do _ <- string "False"
           skipSpace
           return (Left False)

      , do _ <- string "True"
           skipSpace
           return (Left True)

      , do lo <- dRealLoBound

           skipSpace
           _ <- char ','
           skipSpace

           hi <- dRealHiBound

           skipSpace
           _ <- option ' ' (char ';')
           skipSpace
           return (Right (lo,hi))
      ]
    return (Text.fromStrict (decodeUtf8 nm),val)

dRealLoBound :: Parser (Maybe Rational)
dRealLoBound = choice
   [ string "(-inf" >> return Nothing
   , do _ <- char '['
        sign <- option 1 (char '-' >> return (-1))
        num <- takeWhile1 (\c -> c `elem` ("0123456789+-eE." :: String))
        case readFloat (UTF8.toString num) of
          (x,""):_ -> return $ Just (sign * x)
          _ -> fail "expected rational bound"
   ]

dRealHiBound :: Parser (Maybe Rational)
dRealHiBound = choice
   [ string "inf)" >> return Nothing
   , do sign <- option 1 (char '-' >> return (-1))
        num <- takeWhile1 (\c -> c `elem` ("0123456789+-eE." :: String))
        _ <- char ']'
        case readFloat (UTF8.toString num) of
          (x,""):_ -> return $ Just (sign * x)
          _ -> fail "expected rational bound"
   ]


runDRealInOverride
   :: ExprBuilder t st fs
   -> LogData
   -> [BoolExpr t]   -- ^ propositions to check
   -> (SatResult (SMT2.WriterConn t (SMT2.Writer DReal), DRealBindings) () -> IO a)
   -> IO a
runDRealInOverride sym logData ps modelFn = do
  p <- andAllOf sym folded ps
  solver_path <- findSolverPath drealPath (getConfiguration sym)
  logSolverEvent sym
    (SolverStartSATQuery $ SolverStartSATQueryRec
    { satQuerySolverName = "dReal"
    , satQueryReason = logReason logData
    })
  withProcessHandles solver_path ["--model", "--in", "--format", "smt2"] Nothing $ \(in_h, out_h, err_h, ph) -> do

      -- Log stderr to output.
      err_stream <- Streams.handleToInputStream err_h
      void $ forkIO $ logErrorStream err_stream (logCallbackVerbose logData 2)

      -- Write SMTLIB to standard input.
      logCallbackVerbose logData 2 "Sending Satisfiability problem to dReal"
      -- dReal does not support (define-fun ...)
      bindings <- getSymbolVarBimap sym

      out_str  <-
        case logHandle logData of
          Nothing -> Streams.encodeUtf8 =<< Streams.handleToOutputStream in_h
          Just aux_h ->
            do aux_str <- Streams.handleToOutputStream aux_h
               Streams.encodeUtf8 =<< teeOutputStream aux_str =<< Streams.handleToOutputStream in_h

      in_str <- Streams.nullInput

      let cfg = getConfiguration sym
      strictness <- maybe SMTWriter.Strict
                    (\c -> if fromConcreteBool c
                           then SMTWriter.Strict
                           else SMTWriter.Lenient) <$>
                    (getOption =<< getOptionSetting RSP.strictSMTParsing cfg)

      c <- SMT2.newWriter DReal out_str in_str SMTWriter.nullAcknowledgementAction strictness "dReal"
             False useComputableReals False bindings

      -- Set the dReal default logic
      SMT2.setLogic c (SMT2.Logic "QF_NRA")
      SMT2.assume c p

      -- Create stream for output from solver.
      out_stream <- Streams.handleToInputStream out_h

      -- dReal wants to parse its entire input, all the way through <EOF> before it does anything
      -- Also (apparently) you _must_ include the exit command to get any response at all...
      SMT2.writeCheckSat c
      SMT2.writeExit c
      hClose in_h

      logCallbackVerbose logData 2 "Parsing result from solver"

      msat_result <- try $ Streams.parseFromStream dRealResponse out_stream

      res <-
        case msat_result of
          Left ex@Streams.ParseException{} -> fail $ unlines ["Could not parse dReal result.", displayException ex]
          Right (Unsat ()) -> pure (Unsat ())
          Right Unknown    -> pure Unknown
          Right (Sat bs)   -> pure (Sat (c, Map.fromList bs))

      r <- modelFn res

      -- Check error code.
      logCallbackVerbose logData 2 "Waiting for dReal to exit"

      ec <- waitForProcess ph
      case ec of
        ExitSuccess -> do
          -- Return result.
          logCallbackVerbose logData 2 "dReal terminated."

          logSolverEvent sym
             (SolverEndSATQuery $ SolverEndSATQueryRec
             { satQueryResult = forgetModelAndCore res
             , satQueryError  = Nothing
             })

          return r
        ExitFailure exit_code ->
          fail $ "dReal exited with unexpected code: " ++ show exit_code
