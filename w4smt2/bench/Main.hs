{-# LANGUAGE ImportQualifiedPost #-}
module Main (main) where

import Benchmark.Config qualified as Conf
import Benchmark.Discovery qualified as Discovery
import Benchmark.Output qualified as Output
import Benchmark.Runner (CompletedResult(crFilePath, crResult))
import Benchmark.Runner qualified as Runner
import Control.Monad (when)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Map.Strict qualified as Map
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import System.Directory (makeAbsolute)
import System.Exit (die, exitFailure)
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
  hPutStrLn stderr $ "Starting benchmark with " ++ show (Conf.cfgWorkers config') ++ " workers..."
  hPutStrLn stderr ""

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
    let emptyStats = Output.computeStats []
    let initialRunning = min (Conf.cfgWorkers config') (length files)
    Output.updateProgressLine initialRunning 0 (length files) emptyStats (length files)

  let onComplete cr = do
        when isTerm Output.clearProgressLine

        modifyIORef' resultsRef (Map.insert (crFilePath cr) (crResult cr))

        completedResults <- readIORef resultsRef
        let done = Map.size completedResults

        let relativePath = makeRelative baseDir (crFilePath cr)
        Output.logFileResult maybeLogHandle done (length files) relativePath (crResult cr)

        when isTerm $ do
          let partialStats = Output.computeStats (Map.elems completedResults)
          let remaining = length files - done
          let currentlyRunning = min (Conf.cfgWorkers config') remaining
          Output.updateProgressLine currentlyRunning done (length files) partialStats remaining

  results <- Runner.runBenchmark config' files onComplete

  endTime <- getCurrentTime

  when isTerm Output.clearProgressLine

  let stats = Output.computeStats results
  let totalTime = realToFrac $ diffUTCTime endTime startTime

  Output.printSummary stats totalTime

  case maybeLogHandle of
    Just logHandle -> hClose logHandle
    Nothing -> return ()

  when (Output.statsErrors stats > 0) exitFailure
