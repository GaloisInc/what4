{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
module Benchmark.Output
  ( Stats(..)
  , computeStats
  , isTerminal
  , updateProgressLine
  , clearProgressLine
  , logFileResult
  , printSummary
  ) where

import Benchmark.Runner (FileResult(FileError, FileSat, FileTimeout, FileUnknown, FileUnsat, FileUnsupported))
import System.Console.ANSI (hClearLine, hCursorBackward)
import System.Console.ANSI qualified as ANSI
import System.IO (Handle, hIsTerminalDevice, hPutStr, hPutStrLn, stderr)
import Text.Printf (printf)

-- | Statistics accumulator
data Stats = Stats
  { statsTotal :: !Int
  , statsSat :: !Int
  , statsUnsat :: !Int
  , statsUnknown :: !Int
  , statsUnsupported :: !Int
  , statsErrors :: !Int
  , statsTimes :: ![Double]
  , statsZ3Times :: ![Double]
  } deriving (Show)

-- | Compute statistics from a list of file results
computeStats :: [FileResult] -> Stats
computeStats results = foldl addResult emptyStats results
  where
    emptyStats = Stats 0 0 0 0 0 0 [] []

    addResult s = \case
      FileSat t mz3 ->
        s { statsTotal = statsTotal s + 1
          , statsSat = statsSat s + 1
          , statsTimes = t : statsTimes s
          , statsZ3Times = maybe (statsZ3Times s) (: statsZ3Times s) mz3
          }
      FileUnsat t mz3 ->
        s { statsTotal = statsTotal s + 1
          , statsUnsat = statsUnsat s + 1
          , statsTimes = t : statsTimes s
          , statsZ3Times = maybe (statsZ3Times s) (: statsZ3Times s) mz3
          }
      FileUnknown t mz3 ->
        s { statsTotal = statsTotal s + 1
          , statsUnknown = statsUnknown s + 1
          , statsTimes = t : statsTimes s
          , statsZ3Times = maybe (statsZ3Times s) (: statsZ3Times s) mz3
          }
      FileUnsupported t mz3 ->
        s { statsTotal = statsTotal s + 1
          , statsUnsupported = statsUnsupported s + 1
          , statsTimes = t : statsTimes s
          , statsZ3Times = maybe (statsZ3Times s) (: statsZ3Times s) mz3
          }
      FileError _ t mz3 ->
        s { statsTotal = statsTotal s + 1
          , statsErrors = statsErrors s + 1
          , statsTimes = t : statsTimes s
          , statsZ3Times = maybe (statsZ3Times s) (: statsZ3Times s) mz3
          }
      FileTimeout t mz3 ->
        s { statsTotal = statsTotal s + 1
          , statsErrors = statsErrors s + 1
          , statsTimes = t : statsTimes s
          , statsZ3Times = maybe (statsZ3Times s) (: statsZ3Times s) mz3
          }

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
logFileResult :: Maybe Handle -> Int -> Int -> FilePath -> FileResult -> IO ()
logFileResult maybeLogHandle current total filepath result = do
  let prefix = printf "[%d/%d] " current total
  let msg = case result of
        FileSat t mz3 ->
          prefix ++ filepath ++ ": sat in " ++ formatTime t ++ formatZ3Time mz3
        FileUnsat t mz3 ->
          prefix ++ filepath ++ ": unsat in " ++ formatTime t ++ formatZ3Time mz3
        FileUnknown t mz3 ->
          prefix ++ filepath ++ ": unknown in " ++ formatTime t ++ formatZ3Time mz3
        FileUnsupported t mz3 ->
          prefix ++ filepath ++ ": unsupported in " ++ formatTime t ++ formatZ3Time mz3
        FileTimeout t mz3 ->
          prefix ++ "TIMEOUT: " ++ filepath ++ " (>" ++ formatTime t ++ ")" ++ formatZ3Time mz3
        FileError errorMsg t mz3 ->
          prefix ++ "ERROR: " ++ filepath ++ " - " ++ errorMsg ++ " in " ++ formatTime t ++ formatZ3Time mz3

  let stderrMsg = case result of
        FileTimeout _ _ -> prefix ++ colorize ANSI.Red (drop (length prefix) msg)
        FileError _ _ _ -> prefix ++ colorize ANSI.Red (drop (length prefix) msg)
        _ -> msg

  hPutStrLn stderr stderrMsg
  case maybeLogHandle of
    Just logHandle -> hPutStrLn logHandle msg
    Nothing -> return ()
  where
    formatZ3Time Nothing = ""
    formatZ3Time (Just z3t) = " (Z3: " ++ formatTime z3t ++ ")"

-- | Print final summary
printSummary :: Stats -> Double -> IO ()
printSummary stats totalTime = do
  hPutStrLn stderr ""
  hPutStrLn stderr "========================================="
  hPutStrLn stderr "Summary:"
  hPutStrLn stderr $ "  Total files: " ++ show (statsTotal stats)
  hPutStrLn stderr $ "  Sat: " ++ show (statsSat stats)
  hPutStrLn stderr $ "  Unsat: " ++ show (statsUnsat stats)
  hPutStrLn stderr $ "  Unknown: " ++ show (statsUnknown stats)
  hPutStrLn stderr $ "  Unsupported: " ++ show (statsUnsupported stats)
  hPutStrLn stderr $ "  Errors: " ++ show (statsErrors stats)

  let times = statsTimes stats
  if not (null times)
    then do
      let avg = sum times / fromIntegral (length times)
      let variance = sum [(t - avg) ^ (2 :: Int) | t <- times] / fromIntegral (length times)
      let stddev = sqrt variance
      hPutStrLn stderr $ "  Average time: " ++ formatTime avg
      hPutStrLn stderr $ "  Std dev: " ++ formatTime stddev
    else return ()

  let z3Times = statsZ3Times stats
  if not (null z3Times)
    then do
      let z3Avg = sum z3Times / fromIntegral (length z3Times)
      hPutStrLn stderr $ "  Z3 avg verification time: " ++ formatTime z3Avg
      hPutStrLn stderr $ "  Z3 verifications: " ++ show (length z3Times)
    else return ()

  hPutStrLn stderr $ "  Total time: " ++ formatDuration totalTime
  hPutStrLn stderr "========================================="

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
