{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
module Benchmark.Output
  ( Stats(..)
  , SolverStats(..)
  , computeStats
  , isTerminal
  , updateProgressLine
  , clearProgressLine
  , logFileResult
  , printSummary
  ) where

import Benchmark.Config (Solver)
import Benchmark.Runner (FileResult(FileError, FileSat, FileTimeout, FileUnknown, FileUnsat, FileUnsupported), WorkItem, wiFile, wiSolver)
import Control.Monad (when)
import Data.List (sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import System.Console.ANSI (hClearLine, hCursorBackward)
import System.Console.ANSI qualified as ANSI
import System.IO (Handle, hIsTerminalDevice, hPutStr, hPutStrLn, stderr)
import Text.Printf (printf)

-- | Per-solver statistics
data SolverStats = SolverStats
  { ssAvgTime :: !Double
  , ssStdDevTime :: !Double
  , ssMedianTime :: !Double
  , ssTotalTime :: !Double
  , ssUnknown :: !Int
  , ssUnsupported :: !Int
  , ssTimeouts :: !Int
  , ssErrors :: !Int
  , ssTimes :: ![Double]
  } deriving (Show)

-- | Statistics accumulator
data Stats = Stats
  { statsTotal :: !Int
  , statsSat :: !Int
  , statsUnsat :: !Int
  , statsUnknown :: !Int
  , statsUnsupported :: !Int
  , statsErrors :: !Int
  , statsTimes :: ![Double]
  , statsPerSolver :: !(Map Solver SolverStats)
  , statsDisagreements :: ![Text]
  } deriving (Show)

-- | Compute statistics from a map of work items to results
computeStats :: Map WorkItem FileResult -> Stats
computeStats resultsMap =
  let results = Map.toList resultsMap
      -- Group results by file
      byFile = Map.fromListWith (++) [(wiFile wi, [(wiSolver wi, res)]) | (wi, res) <- results]

      -- Check for disagreements
      disagreements = concatMap checkFileAgreement (Map.toList byFile)

      -- Compute overall stats
      overallStats = foldl addResult emptyStats (Map.elems resultsMap)

      -- Compute per-solver stats
      bySolver = Map.fromListWith (++) [(wiSolver wi, [res]) | (wi, res) <- results]
      perSolverStats = Map.map computeSolverStats bySolver
  in overallStats
       { statsPerSolver = perSolverStats
       , statsDisagreements = disagreements
       }
  where
    emptyStats = Stats 0 0 0 0 0 0 [] Map.empty []

    addResult s = \case
      FileSat t ->
        s { statsTotal = statsTotal s + 1
          , statsSat = statsSat s + 1
          , statsTimes = t : statsTimes s
          }
      FileUnsat t ->
        s { statsTotal = statsTotal s + 1
          , statsUnsat = statsUnsat s + 1
          , statsTimes = t : statsTimes s
          }
      FileUnknown t ->
        s { statsTotal = statsTotal s + 1
          , statsUnknown = statsUnknown s + 1
          , statsTimes = t : statsTimes s
          }
      FileUnsupported t ->
        s { statsTotal = statsTotal s + 1
          , statsUnsupported = statsUnsupported s + 1
          , statsTimes = t : statsTimes s
          }
      FileError _ t ->
        s { statsTotal = statsTotal s + 1
          , statsErrors = statsErrors s + 1
          , statsTimes = t : statsTimes s
          }
      FileTimeout t ->
        s { statsTotal = statsTotal s + 1
          , statsErrors = statsErrors s + 1
          , statsTimes = t : statsTimes s
          }

    checkFileAgreement :: (FilePath, [(Solver, FileResult)]) -> [Text]
    checkFileAgreement (file, solverResults) =
      let concreteResults = [(solver, resultType res) | (solver, res) <- solverResults, isConcreteResult res]
          uniqueResults = Map.fromListWith (++) [(rtype, [solver]) | (solver, rtype) <- concreteResults]
      in if Map.size uniqueResults > 1
         then [Text.pack $ "Disagreement on " ++ file ++ ": " ++ show (Map.toList uniqueResults)]
         else []

    isConcreteResult = \case
      FileSat _ -> True
      FileUnsat _ -> True
      _ -> False

    resultType = \case
      FileSat _ -> "sat"
      FileUnsat _ -> "unsat"
      _ -> "other"

    computeSolverStats :: [FileResult] -> SolverStats
    computeSolverStats solverResults =
      let times = map getTime solverResults
          sortedTimes = sort times
          count = length times
          total = sum times
          avg = if count > 0 then total / fromIntegral count else 0
          variance = if count > 0
                     then sum [(t - avg) ^ (2 :: Int) | t <- times] / fromIntegral count
                     else 0
          stddev = sqrt variance
          median = if count > 0
                   then sortedTimes !! (count `div` 2)
                   else 0
          unknowns = length [() | FileUnknown _ <- solverResults]
          unsupported = length [() | FileUnsupported _ <- solverResults]
          timeouts = length [() | FileTimeout _ <- solverResults]
          errors = length [() | FileError _ _ <- solverResults]
      in SolverStats avg stddev median total unknowns unsupported timeouts errors times

    getTime = \case
      FileSat t -> t
      FileUnsat t -> t
      FileUnknown t -> t
      FileUnsupported t -> t
      FileError _ t -> t
      FileTimeout t -> t

-- | Check if stderr is a terminal
isTerminal :: IO Bool
isTerminal = hIsTerminalDevice stderr

-- | Update the progress line (only call if isTerminal is True)
updateProgressLine :: Int -> Int -> Int -> Stats -> Int -> IO ()
updateProgressLine current done total stats remaining = do
  hCursorBackward stderr 1000  -- Move to beginning of line
  hClearLine stderr

  let parts = [ "["
              , colorize ANSI.Blue (printf "%d" current)
              , "/"
              , colorize ANSI.Green (printf "%d" done)
              , printf "/%d]" total
              ]

  let statusParts = concat
        [ if statsErrors stats > 0
            then [colorize ANSI.Red (printf "%d errors" (statsErrors stats))]
            else []
        , if statsUnsupported stats > 0
            then [colorize ANSI.Yellow (printf "%d unsupported" (statsUnsupported stats))]
            else []
        , [ printf
             "%d/%d/%d sat/unsat/unknown"
             (statsSat stats)
             (statsUnsat stats)
             (statsUnknown stats)
          ]
        ]

  -- Calculate estimated time remaining
  let timeEstimate =
        if null (statsTimes stats)
        then ""
        else
          let avg = sum (statsTimes stats) / fromIntegral (length (statsTimes stats))
              remainingTime = avg * fromIntegral remaining
              formatted = if remainingTime >= 120
                          then printf "%dm" (round (remainingTime / 60) :: Int)
                          else printf "%ds" (round remainingTime :: Int)
          in ", ~" ++ formatted ++ " remaining"

  hPutStr stderr $ concat parts ++ " " ++ unwords statusParts ++ timeEstimate

-- | Clear the progress line (only call if isTerminal is True)
clearProgressLine :: IO ()
clearProgressLine = do
  hCursorBackward stderr 1000
  hClearLine stderr

-- | Log a file result
logFileResult :: Maybe Handle -> Int -> Int -> FilePath -> Solver -> FileResult -> IO ()
logFileResult maybeLogHandle current total filepath solver result = do
  let prefix = printf "[%d/%d] " current total
  let solverName = show solver
  let msg = case result of
        FileSat t ->
          prefix ++ solverName ++ " " ++ filepath ++ ": sat in " ++ formatTime t
        FileUnsat t ->
          prefix ++ solverName ++ " " ++ filepath ++ ": unsat in " ++ formatTime t
        FileUnknown t ->
          prefix ++ solverName ++ " " ++ filepath ++ ": unknown in " ++ formatTime t
        FileUnsupported t ->
          prefix ++ solverName ++ " " ++ filepath ++ ": unsupported in " ++ formatTime t
        FileTimeout t ->
          prefix ++ solverName ++ " TIMEOUT: " ++ filepath ++ " (>" ++ formatTime t ++ ")"
        FileError errorMsg t ->
          prefix ++ solverName ++ " ERROR: " ++ filepath ++ " - " ++ errorMsg ++ " in " ++ formatTime t

  let stderrMsg = case result of
        FileTimeout _ -> prefix ++ colorize ANSI.Red (drop (length prefix) msg)
        FileError _ _ -> prefix ++ colorize ANSI.Red (drop (length prefix) msg)
        _ -> msg

  hPutStrLn stderr stderrMsg
  case maybeLogHandle of
    Just logHandle -> hPutStrLn logHandle msg
    Nothing -> return ()

-- | Print final summary
printSummary :: Stats -> Double -> IO ()
printSummary stats totalTime = do
  hPutStrLn stderr ""
  hPutStrLn stderr "========================================="
  hPutStrLn stderr ""

  -- Overall statistics
  hPutStrLn stderr "Overall Statistics:"
  hPutStrLn stderr $ "  Sat: " ++ show (statsSat stats)
  hPutStrLn stderr $ "  Unsat: " ++ show (statsUnsat stats)
  hPutStrLn stderr $ "  Unknown: " ++ show (statsUnknown stats)
  hPutStrLn stderr $ "  Unsupported: " ++ show (statsUnsupported stats)
  hPutStrLn stderr $ "  Errors: " ++ show (statsErrors stats)
  hPutStrLn stderr ""

  -- Per-solver statistics
  if not (Map.null (statsPerSolver stats))
    then do
      hPutStrLn stderr "Per-Solver Statistics:"
      hPutStrLn stderr ""
      mapM_ printSolverStats (Map.toList (statsPerSolver stats))
    else return ()

  -- Disagreements
  if not (null (statsDisagreements stats))
    then do
      hPutStrLn stderr $ colorize ANSI.Red "Disagreements:"
      mapM_ (\d -> hPutStrLn stderr $ "  " ++ Text.unpack d) (statsDisagreements stats)
      hPutStrLn stderr ""
    else do
      hPutStrLn stderr $ colorize ANSI.Green "Disagreements: None"
      hPutStrLn stderr ""

  hPutStrLn stderr $ "Total time: " ++ formatDuration totalTime
  hPutStrLn stderr "========================================="

  where
    printSolverStats :: (Solver, SolverStats) -> IO ()
    printSolverStats (solver, ss) = do
      hPutStrLn stderr $ show solver ++ ":"
      if not (null (ssTimes ss))
        then do
          hPutStrLn stderr $ "  Average time: " ++ formatTime (ssAvgTime ss) ++ " ± " ++ formatTime (ssStdDevTime ss)
          hPutStrLn stderr $ "  Median time: " ++ formatTime (ssMedianTime ss)
          hPutStrLn stderr $ "  Total time: " ++ formatTime (ssTotalTime ss)
        else return ()
      when (ssUnknown ss > 0) $
        hPutStrLn stderr $ "  Unknown: " ++ show (ssUnknown ss)
      when (ssUnsupported ss > 0) $
        hPutStrLn stderr $ "  Unsupported: " ++ show (ssUnsupported ss)
      when (ssTimeouts ss > 0) $
        hPutStrLn stderr $ "  Timeouts: " ++ show (ssTimeouts ss)
      when (ssErrors ss > 0) $
        hPutStrLn stderr $ "  Errors: " ++ show (ssErrors ss)
      hPutStrLn stderr ""

-- | Format time in seconds
formatTime :: Double -> String
formatTime t = printf "%.3fs" t

-- | Format duration with minutes if applicable
formatDuration :: Double -> String
formatDuration t
  | t >= 60 = printf "%dm %.1fs (%.1fs)" mins secs t
  | otherwise = printf "%.1fs" t
  where
    mins = floor t `div` 60 :: Int
    secs = t - fromIntegral (mins * 60)

-- | Colorize text with ANSI color code
colorize :: ANSI.Color -> String -> String
colorize color text =
  ANSI.setSGRCode [ANSI.SetColor ANSI.Foreground ANSI.Vivid color]
  ++ text
  ++ ANSI.setSGRCode [ANSI.Reset]
