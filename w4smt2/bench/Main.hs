{-# LANGUAGE ImportQualifiedPost #-}
module Main (main) where

import Benchmark.Config qualified as Conf
import Benchmark.Discovery qualified as Discovery
import Benchmark.Output qualified as Output
import Benchmark.Runner (CompletedResult(crResult, crWorkItem), WorkItem(WorkItem), wiFile, wiSolver)
import Benchmark.Runner qualified as Runner
import Control.Monad (when)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Map.Strict qualified as Map
import Data.Text.IO qualified as Text
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import System.Console.ANSI qualified as ANSI
import System.Directory (makeAbsolute)
import System.Exit (ExitCode(ExitFailure), die, exitWith, exitFailure)
import System.FilePath (makeRelative)
import System.IO (BufferMode(LineBuffering), IOMode(WriteMode), hClose, hPutStrLn, hSetBuffering, openFile, stderr)

main :: IO ()
main = do
  config <- Conf.parseArgs

  baseDir <- makeAbsolute (Conf.cfgDirectory config)

  hPutStrLn stderr $ "Searching for .smt2 files in " ++ Conf.cfgDirectory config ++ "..."
  files <- Discovery.findSmt2Files (Conf.cfgDirectory config) (Conf.cfgMaxSize config)

  when (null files) $ die "No .smt2 files found"

  hPutStrLn stderr $ "Found " ++ show (length files) ++ " files"

  hPutStrLn stderr "Building w4smt2..."
  w4smt2Path <- Runner.buildW4SMT2
  let config' = config { Conf.cfgW4SMT2Path = w4smt2Path }

  hPutStrLn stderr $ "Using w4smt2 at: " ++ w4smt2Path
  hPutStrLn stderr $ "Solvers: " ++ unwords (map show (Conf.cfgSolvers config'))
  hPutStrLn stderr $ "Starting benchmark with " ++ show (Conf.cfgWorkers config') ++ " workers..."
  hPutStrLn stderr ""

  -- Generate work items: files × solvers
  let workItems = [WorkItem file solver | file <- files, solver <- Conf.cfgSolvers config']

  maybeLogHandle <- case Conf.cfgLogFile config' of
    Just logPath -> do
      h <- openFile logPath WriteMode
      hSetBuffering h LineBuffering
      return (Just h)
    Nothing -> return Nothing

  isTerm <- Output.isTerminal
  resultsRef <- newIORef Map.empty
  startTime <- getCurrentTime

  when isTerm $ do
    let emptyStats = Output.computeStats Map.empty
    let initialRunning = min (Conf.cfgWorkers config') (length workItems)
    Output.updateProgressLine initialRunning 0 (length workItems) emptyStats (length workItems)

  let onComplete cr = do
        when isTerm Output.clearProgressLine

        modifyIORef' resultsRef (Map.insert (crWorkItem cr) (crResult cr))

        completedResults <- readIORef resultsRef
        let done = Map.size completedResults

        let workItem = crWorkItem cr
        let relativePath = makeRelative baseDir (wiFile workItem)
        Output.logFileResult maybeLogHandle done (length workItems) relativePath (wiSolver workItem) (crResult cr)

        when isTerm $ do
          let partialStats = Output.computeStats completedResults
          let remaining = length workItems - done
          let currentlyRunning = min (Conf.cfgWorkers config') remaining
          Output.updateProgressLine currentlyRunning done (length workItems) partialStats remaining

  results <- Runner.runBenchmark config' workItems onComplete

  endTime <- getCurrentTime

  when isTerm Output.clearProgressLine

  let stats = Output.computeStats results
  let totalTime = realToFrac $ diffUTCTime endTime startTime

  Output.printSummary stats totalTime

  case maybeLogHandle of
    Just logHandle -> hClose logHandle
    Nothing -> return ()

  -- Check for disagreements and exit with error if found
  if not (null (Output.statsDisagreements stats))
    then do
      hPutStrLn stderr ""
      hPutStrLn stderr $ colorize ANSI.Red "ERROR: Solvers disagreed on some problems!"
      mapM_ (Text.hPutStrLn stderr) (Output.statsDisagreements stats)
      exitWith (ExitFailure 1)
    else when (Output.statsErrors stats > 0) exitFailure

  where
    colorize :: ANSI.Color -> String -> String
    colorize color text =
      ANSI.setSGRCode [ANSI.SetColor ANSI.Foreground ANSI.Vivid color]
      ++ text
      ++ ANSI.setSGRCode [ANSI.Reset]
