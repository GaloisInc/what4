{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module W2SMT2
  ( main
  ) where

import Data.Parameterized.Nonce qualified as Nonce
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text.IO
import System.Environment qualified as Env
import System.Exit qualified as Exit
import System.IO qualified as IO
import System.IO.Temp qualified as Temp
import System.Process qualified as Proc

import Who2.Builder qualified as W2
import What4.SatResult qualified as WSR

import W4SMT2.Exec (ExecutionResult(ExecutionResult, erResults))
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
      IO.hPutStrLn IO.stderr "Usage: w5smt2 [SOLVER] [FILE]"
      IO.hPutStrLn IO.stderr "  SOLVER: bitwuzla, cvc5, yices, or z3 (optional)"
      IO.hPutStrLn IO.stderr "  FILE: Path to SMT-LIB2 file (optional, reads from stdin if not provided)"
      Exit.exitFailure

main :: IO ()
main = do
  (maybeSolver, maybeFilePath) <- parseArgs
  input <- case maybeFilePath of
    Nothing -> Text.IO.getContents
    Just path -> Text.IO.readFile path
  execResult <- case maybeSolver of
    Nothing -> do
      -- Use w5's internal solver
      let ?logStderr = Text.IO.hPutStrLn IO.stderr
      Nonce.withIONonceGenerator $ \gen -> do
        sym <- W2.newBuilder gen
        Solve.solve sym input
    Just solverName -> do
      -- Call external solver via CLI
      solveWithExternalSolver solverName input
  -- Output all results
  mapM_ outputResult (erResults execResult)
  where
    outputResult result = case result of
      WSR.Sat () -> putStrLn "sat"
      WSR.Unsat () -> putStrLn "unsat"
      WSR.Unknown -> putStrLn "unknown"

-- | Solve by calling an external solver via CLI
solveWithExternalSolver :: String -> Text -> IO ExecutionResult
solveWithExternalSolver solverName input = do
  -- Write input to temporary file
  Temp.withSystemTempFile "w5smt2.smt2" $ \tmpPath tmpHandle -> do
    Text.IO.hPutStr tmpHandle input
    IO.hClose tmpHandle

    -- Get the command for the solver
    let (cmd, args) = getSolverCommand solverName tmpPath

    -- Run the solver
    (_exitCode, stdout, _stderr) <- Proc.readProcessWithExitCode cmd args ""

    -- Parse results from stdout
    let results = parseExternalSolverOutput stdout

    -- Return ExecutionResult
    return $ ExecutionResult
      { erResults = results
      }

-- | Get the command and arguments to run a solver
getSolverCommand :: String -> FilePath -> (String, [String])
getSolverCommand solverName path = case solverName of
  "z3" -> ("z3", [path])
  "yices" -> ("yices-smt2", [path])
  "cvc5" -> ("cvc5", [path])
  "bitwuzla" -> ("bitwuzla", [path])
  _ -> error $ "Unknown solver: " ++ solverName

-- | Parse solver output to extract sat/unsat/unknown results
parseExternalSolverOutput :: String -> [WSR.SatResult () ()]
parseExternalSolverOutput output =
  let outputLines = lines output
      results = [parseResultLine line | line <- outputLines, isResultLine line]
  in results
  where
    isResultLine line =
      let trimmed = Text.strip (Text.pack line)
      in trimmed `elem` ["sat", "unsat", "unknown"]

    parseResultLine line =
      case Text.strip (Text.pack line) of
        "sat" -> WSR.Sat ()
        "unsat" -> WSR.Unsat ()
        "unknown" -> WSR.Unknown
        _ -> WSR.Unknown  -- fallback
