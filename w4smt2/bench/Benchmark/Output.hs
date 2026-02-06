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
  , colorize
  ) where

import Benchmark.Config (Solver)
import Benchmark.Runner qualified as Runner
import Benchmark.Runner (WorkItem, wiFile, wiSolver)
import Control.Monad (when)
import Data.List (nub, sort)
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
  -- Statistics for solved problems only (sat/unsat)
  , ssSolvedAvgTime :: !Double
  , ssSolvedStdDevTime :: !Double
  , ssSolvedMedianTime :: !Double
  , ssSolvedCount :: !Int
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
computeStats :: Map WorkItem Runner.FileResult -> Stats
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
      Runner.FileResults results t ->
        let satCount = length [() | Runner.ResSat <- results]
            unsatCount = length [() | Runner.ResUnsat <- results]
            unknownCount = length [() | Runner.ResUnknown <- results]
        in s { statsTotal = statsTotal s + 1
             , statsSat = statsSat s + satCount
             , statsUnsat = statsUnsat s + unsatCount
             , statsUnknown = statsUnknown s + unknownCount
             , statsTimes = t : statsTimes s
             }
      Runner.FileUnsupported _ ->
        s { statsTotal = statsTotal s + 1
          , statsUnsupported = statsUnsupported s + 1
          -- Don't include unsupported in time averages
          }
      Runner.FileError _ t ->
        s { statsTotal = statsTotal s + 1
          , statsErrors = statsErrors s + 1
          , statsTimes = t : statsTimes s
          }
      Runner.FileTimeout t ->
        s { statsTotal = statsTotal s + 1
          , statsErrors = statsErrors s + 1
          , statsTimes = t : statsTimes s
          }

    checkFileAgreement :: (FilePath, [(Solver, Runner.FileResult)]) -> [Text]
    checkFileAgreement (file, solverResults) =
      let concreteResults = [(solver, getResults res) | (solver, res) <- solverResults, isConcreteResult res]
          -- Find pairs of solvers that disagree
          disagreements = [(s1, s2) | (s1, r1) <- concreteResults, (s2, r2) <- concreteResults, s1 < s2, resultsDisagree r1 r2]
      in if null disagreements
         then []
         else
           let allDisagreingSolvers = nub $ sort $ concatMap (\(s1, s2) -> [s1, s2]) disagreements
               hasMulti = any hasMultiple [res | (_, res) <- solverResults, isConcreteResult res]
               formatDisagreement = if hasMulti
                 then "Disagreement on " ++ file ++ " between: " ++ unwords (map show allDisagreingSolvers)
                 else
                   -- Single result case: show which solvers had which results
                   let groupedBySolver = [(s, r) | (s, r) <- concreteResults, s `elem` allDisagreingSolvers]
                   in "Disagreement on " ++ file ++ ": " ++ show groupedBySolver
           in [Text.pack formatDisagreement]

    isConcreteResult = \case
      Runner.FileResults _ _ -> True
      _ -> False

    hasMultiple = \case
      Runner.FileResults results _ -> length results > 1
      _ -> False

    getResults = \case
      Runner.FileResults results _ -> results
      _ -> []

    -- Two result sequences disagree if:
    -- 1. They have different lengths, OR
    -- 2. At any position where both have concrete results, those results differ.
    --    Unknown matches any result.
    resultsDisagree :: [Runner.Result] -> [Runner.Result] -> Bool
    resultsDisagree r1 r2
      | length r1 /= length r2 = True
      | otherwise = or $ zipWith disagreeAtPosition r1 r2

    disagreeAtPosition :: Runner.Result -> Runner.Result -> Bool
    disagreeAtPosition Runner.ResUnknown _ = False  -- Unknown matches anything
    disagreeAtPosition _ Runner.ResUnknown = False  -- Unknown matches anything
    disagreeAtPosition a b = a /= b  -- Concrete results must match

    computeSolverStats :: [Runner.FileResult] -> SolverStats
    computeSolverStats solverResults =
      let -- All times (excluding unsupported)
          times = [t | r <- solverResults, Just t <- [getTime r]]
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

          -- Solved times (sat/unsat only)
          solvedTimes = [t | r <- solverResults, Just t <- [getSolvedTime r]]
          sortedSolvedTimes = sort solvedTimes
          solvedCount = length solvedTimes
          solvedAvg = if solvedCount > 0 then sum solvedTimes / fromIntegral solvedCount else 0
          solvedVariance = if solvedCount > 0
                           then sum [(t - solvedAvg) ^ (2 :: Int) | t <- solvedTimes] / fromIntegral solvedCount
                           else 0
          solvedStddev = sqrt solvedVariance
          solvedMedian = if solvedCount > 0
                         then sortedSolvedTimes !! (solvedCount `div` 2)
                         else 0

          unknowns = sum [length [() | Runner.ResUnknown <- rs] | Runner.FileResults rs _ <- solverResults]
          unsupported = length [() | Runner.FileUnsupported _ <- solverResults]
          timeouts = length [() | Runner.FileTimeout _ <- solverResults]
          errors = length [() | Runner.FileError _ _ <- solverResults]
      in SolverStats avg stddev median total solvedAvg solvedStddev solvedMedian solvedCount unknowns unsupported timeouts errors times

    -- Get time for all problems (excludes unsupported)
    getTime = \case
      Runner.FileResults _ t -> Just t
      Runner.FileUnsupported _ -> Nothing
      Runner.FileError _ t -> Just t
      Runner.FileTimeout t -> Just t

    -- Get time for solved problems only (sat/unsat)
    getSolvedTime = \case
      Runner.FileResults results t
        | any isSolved results -> Just t
        | otherwise -> Nothing
      _ -> Nothing

    isSolved = \case
      Runner.ResSat -> True
      Runner.ResUnsat -> True
      Runner.ResUnknown -> False

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
logFileResult :: Maybe Handle -> Int -> Int -> FilePath -> Solver -> Runner.FileResult -> IO ()
logFileResult maybeLogHandle current total filepath solver result = do
  let prefix = printf "[%d/%d] " current total
  let solverName = show solver
  let msg = case result of
        Runner.FileResults results t ->
          let resultStr = case results of
                [] -> "no results"
                [r] -> Text.unpack $ Runner.formatResult r
                _ -> "<multiple>"
          in prefix ++ solverName ++ " " ++ filepath ++ ": " ++ resultStr ++ " in " ++ formatTime t
        Runner.FileUnsupported t ->
          prefix ++ solverName ++ " " ++ filepath ++ ": unsupported in " ++ formatTime t
        Runner.FileTimeout t ->
          prefix ++ solverName ++ " TIMEOUT: " ++ filepath ++ " (>" ++ formatTime t ++ ")"
        Runner.FileError errorMsg t ->
          prefix ++ solverName ++ " ERROR: " ++ filepath ++ " - " ++ errorMsg ++ " in " ++ formatTime t

  let stderrMsg = case result of
        Runner.FileTimeout _ -> prefix ++ colorize ANSI.Red (drop (length prefix) msg)
        Runner.FileError _ _ -> prefix ++ colorize ANSI.Red (drop (length prefix) msg)
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
          hPutStrLn stderr $ "  Average time (all): " ++ formatTime (ssAvgTime ss) ++ " ± " ++ formatTime (ssStdDevTime ss)
          hPutStrLn stderr $ "  Median time (all): " ++ formatTime (ssMedianTime ss)
          when (ssSolvedCount ss > 0) $ do
            hPutStrLn stderr $ "  Average time (sat/unsat): " ++ formatTime (ssSolvedAvgTime ss) ++ " ± " ++ formatTime (ssSolvedStdDevTime ss)
            hPutStrLn stderr $ "  Median time (sat/unsat): " ++ formatTime (ssSolvedMedianTime ss)
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
