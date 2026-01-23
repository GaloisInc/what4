{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Benchmark.Runner
  ( CompletedResult(..)
  , FileResult(..)
  , RunningProcess(..)
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

-- | Result for a single file
data FileResult
  = FileSat !Double
  | FileUnsat !Double
  | FileUnknown !Double
  | FileUnsupported !Double
  | FileError !String !Double
  | FileTimeout !Double
  deriving (Show, Eq)

data ProcessType
  = W4SMT2Process
  | Z3VerifyProcess !FileResult
  deriving (Show, Eq)

data CompletedResult = CompletedResult
  { crFilePath :: !FilePath
  , crResult :: !FileResult
  }

data ProcessCheck
  = StillRunning
  | Finished !CompletedResult
  | NeedsVerification !RunningProcess

-- | Running process tracking
data RunningProcess = RunningProcess
  { rpHandle :: !Proc.ProcessHandle
  , rpFilePath :: !FilePath
  , rpStartTime :: !UTCTime
  , rpStdoutHandle :: !Handle
  , rpStderrHandle :: !Handle
  , rpProcessType :: !ProcessType
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

-- | Start a process for a single file
startProcess :: Conf.Config -> FilePath -> IO RunningProcess
startProcess config filepath = do
  startTime <- getCurrentTime
  (_, Just hout, Just herr, ph) <- Proc.createProcess (Proc.proc (Conf.cfgW4SMT2Path config) [filepath])
    { Proc.std_out = Proc.CreatePipe
    , Proc.std_err = Proc.CreatePipe
    }
  return $ RunningProcess
    { rpHandle = ph
    , rpFilePath = filepath
    , rpStartTime = startTime
    , rpStdoutHandle = hout
    , rpStderrHandle = herr
    , rpProcessType = W4SMT2Process
    }

startZ3Process :: Conf.Config -> FilePath -> FileResult -> IO RunningProcess
startZ3Process config filepath originalResult = do
  startTime <- getCurrentTime
  (_, Just hout, Just herr, ph) <- Proc.createProcess (Proc.proc (Conf.cfgZ3Path config) [filepath])
    { Proc.std_out = Proc.CreatePipe
    , Proc.std_err = Proc.CreatePipe
    }
  return $ RunningProcess
    { rpHandle = ph
    , rpFilePath = filepath
    , rpStartTime = startTime
    , rpStdoutHandle = hout
    , rpStderrHandle = herr
    , rpProcessType = Z3VerifyProcess originalResult
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
        { crFilePath = rpFilePath rp
        , crResult = FileTimeout (Conf.cfgTimeout config)
        }
    else do
      maybeExit <- Proc.getProcessExitCode (rpHandle rp)
      case maybeExit of
        Nothing -> return StillRunning
        Just exitCode -> do
          stdout <- Text.hGetContents (rpStdoutHandle rp)
          stderr <- Text.hGetContents (rpStderrHandle rp)

          case rpProcessType rp of
            W4SMT2Process -> do
              let result = parseResult exitCode stdout stderr elapsed
              if Conf.cfgVerifyZ3 config && needsVerification result
                then do
                  z3Process <- startZ3Process config (rpFilePath rp) result
                  return $ NeedsVerification z3Process
                else
                  return $ Finished $ CompletedResult
                    { crFilePath = rpFilePath rp
                    , crResult = result
                    }

            Z3VerifyProcess originalResult -> do
              let z3Output = Text.words $ Text.toLower stdout
              let finalResult = verifyZ3Output originalResult z3Output
              return $ Finished $ CompletedResult
                { crFilePath = rpFilePath rp
                , crResult = finalResult
                }
  where
    needsVerification = \case
      FileSat _ -> True
      FileUnsat _ -> True
      _ -> False

    verifyZ3Output originalResult z3Output =
      case originalResult of
        FileSat elapsed ->
          if "sat" `elem` z3Output
            then originalResult
            else FileError ("Z3 disagreement: w4smt2 said sat but Z3 said " ++ Text.unpack (Text.unwords z3Output)) elapsed
        FileUnsat elapsed ->
          if "unsat" `elem` z3Output
            then originalResult
            else FileError ("Z3 disagreement: w4smt2 said unsat but Z3 said " ++ Text.unpack (Text.unwords z3Output)) elapsed
        _ -> originalResult

-- | Parse the result from w4smt2 output
parseResult :: ExitCode -> Text -> Text -> Double -> FileResult
parseResult exitCode stdout _stderr elapsed =
  case exitCode of
    ExitFailure 2 -> FileUnsupported elapsed
    ExitFailure _ -> FileError "Non-zero exit code" elapsed
    ExitSuccess ->
      let output = Text.words $ Text.toLower stdout
      in if "sat" `elem` output
         then FileSat elapsed
         else if "unsat" `elem` output
              then FileUnsat elapsed
              else if "unknown" `elem` output
                   then FileUnknown elapsed
                   else FileError "Could not parse output" elapsed

-- | Run benchmark on all files
runBenchmark :: Conf.Config -> [FilePath] -> (CompletedResult -> IO ()) -> IO [FileResult]
runBenchmark config files onComplete = do
  let totalFiles = length files
  let numWorkers = min (Conf.cfgWorkers config) totalFiles

  initialProcesses <- mapM (startProcess config) (take numWorkers files)
  loop totalFiles initialProcesses numWorkers Map.empty

  where

    loop :: Int -> [RunningProcess] -> Int -> Map FilePath FileResult -> IO [FileResult]
    loop _ [] _ results =
      return $ map (results Map.!) files

    loop totalFiles running nextIdx results = do
      (finishedResults, stillRunning) <- checkProcesses [] [] running

      newResults <- foldM (\acc cr -> do
        onComplete cr
        return $ Map.insert (crFilePath cr) (crResult cr) acc
        ) results finishedResults

      let numFinished = length finishedResults
      let numToStart = min numFinished (totalFiles - nextIdx)
      newProcesses <- mapM (startProcess config) (take numToStart (drop nextIdx files))

      let allRunning = stillRunning ++ newProcesses
      let nextIdx' = nextIdx + numToStart

      threadDelay 10000

      loop totalFiles allRunning nextIdx' newResults

    checkProcesses :: [CompletedResult] -> [RunningProcess] -> [RunningProcess] -> IO ([CompletedResult], [RunningProcess])
    checkProcesses finished stillRunning = \case
      [] -> return (finished, stillRunning)
      p:ps -> do
        check <- checkAndCollect config p
        case check of
          StillRunning -> checkProcesses finished (p:stillRunning) ps
          Finished completedResult -> checkProcesses (completedResult:finished) stillRunning ps
          NeedsVerification z3Process -> checkProcesses finished (z3Process:stillRunning) ps
