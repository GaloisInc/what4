{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Benchmark.Runner
  ( CompletedResult(..)
  , FileResult(..)
  , RunningProcess(..)
  , WorkItem(..)
  , buildW4SMT2
  , runBenchmark
  ) where

import Benchmark.Config qualified as Conf
import Control.Concurrent (threadDelay)
import Control.Monad (foldM)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Time.Clock (UTCTime, diffUTCTime, getCurrentTime)
import System.Exit (ExitCode(ExitFailure, ExitSuccess))
import System.IO (Handle)
import System.Process qualified as Proc

-- | Work item representing a (file, solver) pair
data WorkItem = WorkItem
  { wiFile :: !FilePath
  , wiSolver :: !Conf.Solver
  } deriving (Eq, Ord, Show)

-- | Result for a single file
data FileResult
  = FileSat !Double
  | FileUnsat !Double
  | FileUnknown !Double
  | FileUnsupported !Double
  | FileError !String !Double
  | FileTimeout !Double
  deriving (Show, Eq)

data CompletedResult = CompletedResult
  { crWorkItem :: !WorkItem
  , crResult :: !FileResult
  }

data ProcessCheck
  = StillRunning
  | Finished !CompletedResult

-- | Running process tracking
data RunningProcess = RunningProcess
  { rpHandle :: !Proc.ProcessHandle
  , rpWorkItem :: !WorkItem
  , rpStartTime :: !UTCTime
  , rpStdoutHandle :: !Handle
  , rpStderrHandle :: !Handle
  }

-- | Build w4smt2 and return the path to the executable

buildW4SMT2 :: IO FilePath
buildW4SMT2 = do
  _ <- readCreateProcess (Proc.proc "cabal" ["build", "-O2", "exe:w4smt2"])
  path <- readCreateProcess (Proc.proc "cabal" ["list-bin", "exe:w4smt2"])
  return $ Text.unpack $ Text.strip path
  where
    readCreateProcess p = do
      (_, Just hout, _, ph) <- Proc.createProcess p { Proc.std_out = Proc.CreatePipe }
      output <- Text.hGetContents hout
      _ <- Proc.waitForProcess ph
      return output

-- | Start a process for a single work item
startProcess :: Conf.Config -> WorkItem -> IO RunningProcess
startProcess config workItem = do
  startTime <- getCurrentTime
  let createProc = Conf.solverCommand config (wiSolver workItem) (wiFile workItem)
  (_, Just hout, Just herr, ph) <- Proc.createProcess createProc
    { Proc.std_out = Proc.CreatePipe
    , Proc.std_err = Proc.CreatePipe
    }
  return $ RunningProcess
    { rpHandle = ph
    , rpWorkItem = workItem
    , rpStartTime = startTime
    , rpStdoutHandle = hout
    , rpStderrHandle = herr
    }

-- | Check if a process has finished and collect its result
checkAndCollect :: Conf.Config -> RunningProcess -> IO ProcessCheck
checkAndCollect config rp = do
  currentTime <- getCurrentTime
  let elapsed = realToFrac $ diffUTCTime currentTime (rpStartTime rp)

  if elapsed > Conf.cfgTimeout config
    then do
      Proc.terminateProcess (rpHandle rp)
      _ <- Proc.waitForProcess (rpHandle rp)
      return $ Finished $ CompletedResult
        { crWorkItem = rpWorkItem rp
        , crResult = FileTimeout (Conf.cfgTimeout config)
        }
    else do
      maybeExit <- Proc.getProcessExitCode (rpHandle rp)
      case maybeExit of
        Nothing -> return StillRunning
        Just exitCode -> do
          stdout <- Text.hGetContents (rpStdoutHandle rp)
          stderr <- Text.hGetContents (rpStderrHandle rp)
          let result = parseResult exitCode stdout stderr elapsed
          return $ Finished $ CompletedResult
            { crWorkItem = rpWorkItem rp
            , crResult = result
            }

-- | Parse the result from solver output
parseResult :: ExitCode -> Text -> Text -> Double -> FileResult
parseResult exitCode stdout _stderr elapsed =
  case exitCode of
    ExitFailure 2 -> FileUnsupported elapsed
    ExitFailure _ -> FileError "Non-zero exit code" elapsed
    ExitSuccess ->
      let output = Text.strip $ Text.toLower stdout
      in case output of
           "sat" -> FileSat elapsed
           "unsat" -> FileUnsat elapsed
           "unknown" -> FileUnknown elapsed
           _ -> FileError ("Could not parse output: " ++ Text.unpack output) elapsed

-- | Run benchmark on all work items
runBenchmark :: Conf.Config -> [WorkItem] -> (CompletedResult -> IO ()) -> IO (Map WorkItem FileResult)
runBenchmark config workItems onComplete = do
  let totalWorkItems = length workItems
  let numWorkers = min (Conf.cfgWorkers config) totalWorkItems

  initialProcesses <- mapM (startProcess config) (take numWorkers workItems)
  loop totalWorkItems initialProcesses numWorkers Map.empty

  where

    loop :: Int -> [RunningProcess] -> Int -> Map WorkItem FileResult -> IO (Map WorkItem FileResult)
    loop _ [] _ results =
      return results

    loop totalWorkItems running nextIdx results = do
      (finishedResults, stillRunning) <- checkProcesses [] [] running

      newResults <- foldM (\acc cr -> do
        onComplete cr
        return $ Map.insert (crWorkItem cr) (crResult cr) acc
        ) results finishedResults

      let numFinished = length finishedResults
      let numToStart = min numFinished (totalWorkItems - nextIdx)
      newProcesses <- mapM (startProcess config) (take numToStart (drop nextIdx workItems))

      let allRunning = stillRunning ++ newProcesses
      let nextIdx' = nextIdx + numToStart

      threadDelay 10000

      loop totalWorkItems allRunning nextIdx' newResults

    checkProcesses :: [CompletedResult] -> [RunningProcess] -> [RunningProcess] -> IO ([CompletedResult], [RunningProcess])
    checkProcesses finished stillRunning = \case
      [] -> return (finished, stillRunning)
      p:ps -> do
        check <- checkAndCollect config p
        case check of
          StillRunning -> checkProcesses finished (p:stillRunning) ps
          Finished completedResult -> checkProcesses (completedResult:finished) stillRunning ps
