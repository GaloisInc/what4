{-# LANGUAGE ImportQualifiedPost #-}
module Main (main) where

import Benchmark.Config qualified as Conf
import Benchmark.CSV qualified as CSV
import Benchmark.Discovery qualified as Discovery
import Benchmark.Output qualified as Output
import Benchmark.Runner (CompletedResult(crResult, crWorkItem), WorkItem(WorkItem), wiFile, wiSolver)
import Benchmark.Runner qualified as Runner
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.Map.Strict qualified as Map
import Data.Text.IO qualified as Text
import Data.Time.Clock (UTCTime, diffUTCTime, getCurrentTime)
import System.Console.ANSI qualified as ANSI
import System.Directory (doesFileExist, makeAbsolute)
import System.Exit (ExitCode(ExitFailure), die, exitWith, exitFailure)
import System.FilePath (makeRelative)
import System.IO (BufferMode(LineBuffering), IOMode(WriteMode), hClose, hPutStrLn, hSetBuffering, openFile, stderr)
import System.Posix.Signals qualified as Signals

main :: IO ()
main = do
  config <- Conf.parseArgs

  baseDir <- makeAbsolute (Conf.cfgDirectory config)

  -- Read existing results from CSV file, or initialize if it doesn't exist
  csvExists <- doesFileExist (Conf.cfgCSVFile config)
  existingResults <- if csvExists
    then do
      hPutStrLn stderr $ "Reading existing results from " ++ Conf.cfgCSVFile config ++ "..."
      CSV.readResults (Conf.cfgCSVFile config)
    else do
      hPutStrLn stderr $ "Initializing new CSV file: " ++ Conf.cfgCSVFile config
      CSV.writeHeader (Conf.cfgCSVFile config)
      return Map.empty

  hPutStrLn stderr $ "Found " ++ show (Map.size existingResults) ++ " existing results"

  hPutStrLn stderr $ "Searching for .smt2 files in " ++ Conf.cfgDirectory config ++ "..."
  files <- Discovery.findSmt2Files (Conf.cfgDirectory config) (Conf.cfgMaxSize config)

  when (null files) $ die "No .smt2 files found"

  hPutStrLn stderr $ "Found " ++ show (length files) ++ " files"

  hPutStrLn stderr "Building w4smt2..."
  w4smt2Path <- Runner.buildW4SMT2
  let config' = config { Conf.cfgW4SMT2Path = w4smt2Path }

  hPutStrLn stderr $ "Using w4smt2 at: " ++ w4smt2Path
  hPutStrLn stderr $ "Solvers: " ++ unwords (map show (Conf.cfgSolvers config'))

  -- Generate work items: files × solvers, filtering out already completed ones
  let allWorkItems = [WorkItem file solver | file <- files, solver <- Conf.cfgSolvers config']
  let workItems = filter (\wi -> not (Map.member wi existingResults)) allWorkItems

  hPutStrLn stderr $ "Total work items: " ++ show (length allWorkItems)
  hPutStrLn stderr $ "Already completed: " ++ show (length allWorkItems - length workItems)
  hPutStrLn stderr $ "Remaining work items: " ++ show (length workItems)

  when (not (null workItems)) $ do
    hPutStrLn stderr $ "Starting benchmark with " ++ show (Conf.cfgWorkers config') ++ " workers..."
    hPutStrLn stderr ""

  maybeLogHandle <- case Conf.cfgLogFile config' of
    Just logPath -> do
      h <- openFile logPath WriteMode
      hSetBuffering h LineBuffering
      return (Just h)
    Nothing -> return Nothing

  isTerm <- Output.isTerminal
  -- Initialize results with existing results from CSV
  resultsRef <- newIORef existingResults
  startTime <- getCurrentTime

  -- Install SIGINT handler to output summary when interrupted
  _ <- Signals.installHandler Signals.sigINT (Signals.Catch (handleInterrupt isTerm resultsRef startTime)) Nothing

  let totalWorkItems = length allWorkItems
  let alreadyDone = Map.size existingResults

  when isTerm $ do
    let initialStats = Output.computeStats existingResults
    let initialRunning = min (Conf.cfgWorkers config') (length workItems)
    Output.updateProgressLine initialRunning alreadyDone totalWorkItems initialStats (length workItems)

  let onComplete cr = do
        when isTerm Output.clearProgressLine

        -- Append result to CSV file
        CSV.appendResult (Conf.cfgCSVFile config') (crWorkItem cr) (crResult cr)

        modifyIORef' resultsRef (Map.insert (crWorkItem cr) (crResult cr))

        completedResults <- readIORef resultsRef
        let done = Map.size completedResults

        let workItem = crWorkItem cr
        let relativePath = makeRelative baseDir (wiFile workItem)
        Output.logFileResult maybeLogHandle done totalWorkItems relativePath (wiSolver workItem) (crResult cr)

        when isTerm $ do
          let partialStats = Output.computeStats completedResults
          let remaining = totalWorkItems - done
          let currentlyRunning = min (Conf.cfgWorkers config') remaining
          Output.updateProgressLine currentlyRunning done totalWorkItems partialStats remaining

  _ <- Runner.runBenchmark config' workItems onComplete

  endTime <- getCurrentTime

  when isTerm Output.clearProgressLine

  -- Get final results including both existing and newly completed
  results <- readIORef resultsRef
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
    handleInterrupt :: Bool -> IORef (Map.Map Runner.WorkItem Runner.FileResult) -> UTCTime -> IO ()
    handleInterrupt isTerm resultsRef startTime = do
      when isTerm Output.clearProgressLine
      hPutStrLn stderr ""
      hPutStrLn stderr $ colorize ANSI.Yellow "Interrupted! Printing summary of completed work..."
      hPutStrLn stderr ""
      results <- readIORef resultsRef
      endTime <- getCurrentTime
      let stats = Output.computeStats results
      let totalTime = realToFrac $ diffUTCTime endTime startTime
      Output.printSummary stats totalTime
      exitWith (ExitFailure 130)  -- 130 is standard exit code for SIGINT (128 + 2)

    colorize :: ANSI.Color -> String -> String
    colorize color text =
      ANSI.setSGRCode [ANSI.SetColor ANSI.Foreground ANSI.Vivid color]
      ++ text
      ++ ANSI.setSGRCode [ANSI.Reset]
