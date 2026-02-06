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
import System.Posix.Signals qualified as Signals

import What4.Expr qualified as WE
import What4.FloatMode qualified as WFM
import What4.SatResult qualified as WSR

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
  -- Install signal handler for SIGTERM to ensure clean shutdown.
  --
  -- When SIGTERM is received (e.g., from the w4smt2-bench timeout mechanismg),
  -- the handler calls exitWith which triggers Haskell's exception unwinding
  -- mechanism. This allows the What4 library's bracket-style functions (withZ3,
  -- withCVC5, withBitwuzla, etc.) to run their cleanup code, which properly
  -- terminates any running solver subprocesses. Without this handler, solver
  -- processes would be orphaned when w4smt2 is terminated.
  --
  -- Exit code 143 is the standard convention for SIGTERM (128 + 15).
  _ <- Signals.installHandler Signals.sigTERM (Signals.Catch handleSignal) Nothing

  (maybeSolver, maybeFilePath) <- parseArgs
  input <- case maybeFilePath of
    Nothing -> Text.IO.getContents
    Just path -> Text.IO.readFile path
  maybeResult <- let ?logStderr = Text.IO.hPutStrLn IO.stderr
                     ?writeStdout = Text.IO.putStrLn
                 in Nonce.withIONonceGenerator $ \gen -> do
      sym <- WE.newExprBuilder WFM.FloatUninterpretedRepr WE.EmptyExprBuilderState gen
      case maybeSolver of
        Nothing -> Just <$> Solve.solve sym input
        Just solverName -> Solve.solveWithSolver solverName sym input
  case maybeResult of
    Nothing -> do
      IO.hPutStrLn IO.stderr "Error: Unknown solver"
      Exit.exitFailure
    Just result -> case result of
      WSR.Sat () -> putStrLn "sat"
      WSR.Unsat () -> putStrLn "unsat"
      WSR.Unknown -> putStrLn "unknown"

  where
    handleSignal = Exit.exitWith (Exit.ExitFailure 143)
