{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Benchmark.CSV
  ( readResults
  , writeHeader
  , appendResult
  ) where

import Benchmark.Config ()
import Benchmark.Runner qualified as Runner
import Control.Exception (catch, IOException)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text.IO
import System.IO (IOMode(AppendMode, WriteMode), hClose, hPutStrLn, openFile)
import Text.Read (readMaybe)

-- | Read existing results from CSV file
readResults :: FilePath -> IO (Map Runner.WorkItem Runner.FileResult)
readResults csvPath = do
  contents <- (Text.IO.readFile csvPath) `catch` handleMissing
  let lns = drop 1 $ Text.lines contents  -- Skip header
  parsed <- mapM parseResultLine $ filter (not . Text.null) lns
  return $ Map.fromList parsed
  where
    handleMissing :: IOException -> IO Text
    handleMissing _ = return Text.empty

    parseResultLine :: Text -> IO (Runner.WorkItem, Runner.FileResult)
    parseResultLine line =
      let parts = Text.splitOn "," line
      in case parts of
           [file, solver, result, timeStr] ->
             let wi = Runner.WorkItem (Text.unpack file) (read $ Text.unpack solver)
                 time = maybe 0 id (readMaybe $ Text.unpack timeStr)
                 fr = parseResult result time
             in return (wi, fr)
           _ -> fail $ "Invalid CSV line: " ++ Text.unpack line

    parseResult :: Text -> Double -> Runner.FileResult
    parseResult result time = case result of
      "sat" -> Runner.FileSat time
      "unsat" -> Runner.FileUnsat time
      "unknown" -> Runner.FileUnknown time
      "unsupported" -> Runner.FileUnsupported time
      "timeout" -> Runner.FileTimeout time
      _ -> Runner.FileError (Text.unpack result) time

-- | Write CSV header
writeHeader :: FilePath -> IO ()
writeHeader csvPath = do
  h <- openFile csvPath WriteMode
  hPutStrLn h "file,solver,result,time"
  hClose h

-- | Append a result to CSV file
appendResult :: FilePath -> Runner.WorkItem -> Runner.FileResult -> IO ()
appendResult csvPath wi fr = do
  h <- openFile csvPath AppendMode
  hPutStrLn h $ formatResultLine wi fr
  hClose h

formatResultLine :: Runner.WorkItem -> Runner.FileResult -> String
formatResultLine wi fr =
  let file = Runner.wiFile wi
      solver = show (Runner.wiSolver wi)
      (result, time) = case fr of
        Runner.FileSat t -> ("sat", t)
        Runner.FileUnsat t -> ("unsat", t)
        Runner.FileUnknown t -> ("unknown", t)
        Runner.FileUnsupported t -> ("unsupported", t)
        Runner.FileTimeout t -> ("timeout", t)
        Runner.FileError msg t -> ("error: " ++ msg, t)
  in file ++ "," ++ solver ++ "," ++ result ++ "," ++ show time
