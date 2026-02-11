{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module W4SMT2
  ( main
  ) where

import Data.Parameterized.Nonce qualified as Nonce
import Data.Text.IO qualified as Text.IO
import System.Environment qualified as Env
import System.Exit qualified as Exit
import System.IO qualified as IO

import What4.Expr qualified as WE
import What4.FloatMode qualified as WFM
import What4.SatResult qualified as WSR

import W4SMT2.Exec (ExecutionResult(erResults))
import W4SMT2.Solve qualified as Solve

validSolvers :: [String]
validSolvers = ["bitwuzla", "cvc5", "yices", "z3"]

parseArgs :: IO (Maybe String, Maybe FilePath)
parseArgs = do
  args <- Env.getArgs
  case args of
    [] -> return (Nothing, Nothing)
    [arg] -> if arg `elem` validSolvers
             then return (Just arg, Nothing)
             else return (Nothing, Just arg)
    [solver, file] -> if solver `elem` validSolvers
                      then return (Just solver, Just file)
                      else usage
    _ -> usage
  where
    usage = do
      IO.hPutStrLn IO.stderr "Usage: w4smt2 [SOLVER] [FILE]"
      IO.hPutStrLn IO.stderr "  SOLVER: bitwuzla, cvc5, yices, or z3 (optional)"
      IO.hPutStrLn IO.stderr "  FILE: Path to SMT-LIB2 file (optional, reads from stdin if not provided)"
      Exit.exitFailure

main :: IO ()
main = do
  (maybeSolver, maybeFilePath) <- parseArgs
  input <- case maybeFilePath of
    Nothing -> Text.IO.getContents
    Just path -> Text.IO.readFile path
  maybeExecResult <- let ?logStderr = Text.IO.hPutStrLn IO.stderr
                     in Nonce.withIONonceGenerator $ \gen -> do
      sym <- WE.newExprBuilder WFM.FloatUninterpretedRepr WE.EmptyExprBuilderState gen
      case maybeSolver of
        Nothing -> Just <$> Solve.solve sym input
        Just solverName -> Solve.solveWithSolver solverName sym input
  case maybeExecResult of
    Nothing -> do
      IO.hPutStrLn IO.stderr "Error: Unknown solver"
      Exit.exitFailure
    Just execResult -> do
      -- Output all results
      mapM_ outputResult (erResults execResult)
  where
    outputResult result = case result of
      WSR.Sat () -> putStrLn "sat"
      WSR.Unsat () -> putStrLn "unsat"
      WSR.Unknown -> putStrLn "unknown"
