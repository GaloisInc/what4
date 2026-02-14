{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.Simplification
  ( discoverSimplificationTests
  , discoverZ3ValidationTests
  ) where

import Control.Exception (catch, SomeException)
import Data.List (sort)
import Data.Parameterized.Nonce (withIONonceGenerator)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as TIO
import System.Directory (listDirectory)
import System.Exit (ExitCode(ExitSuccess))
import System.FilePath ((</>), takeExtension, dropExtension)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (testCase, assertEqual, assertFailure)
import What4.SatResult (SatResult(Sat, Unsat, Unknown))

import W4SMT2.Exec (ExecutionResult(erResults))
import W4SMT2.Solve (solve)
import Who2.Builder (newBuilder)

-- | Discover all .smt2 files in a directory and create simplification tests
discoverSimplificationTests :: FilePath -> IO [TestTree]
discoverSimplificationTests dir = discoverTests dir mkSimplTest

-- | Discover all .smt2 files in a directory and create z3 validation tests
discoverZ3ValidationTests :: FilePath -> IO [TestTree]
discoverZ3ValidationTests dir = discoverTests dir mkZ3ValidationTest

-- | Discover all .smt2 files in a directory
discoverTests :: FilePath -> (FilePath -> FilePath -> IO TestTree) -> IO [TestTree]
discoverTests dir mkTest = do
  files <- listDirectory dir
  let smt2Files = sort $ filter (\f -> takeExtension f == ".smt2") files
  mapM (mkTest dir) smt2Files

-- | Parse expected results from comments after (check-sat)
-- Example: "(check-sat) ; sat" -> ["sat"]
-- Skips lines that are commented out (start with ;)
parseExpectations :: Text -> [Text]
parseExpectations input =
  [ expectation
  | line <- Text.lines input
  , let stripped = Text.strip line
  , not (Text.isPrefixOf ";" stripped)  -- Skip commented-out lines
  , "(check-sat)" `Text.isInfixOf` line
  , let parts = Text.splitOn ";" line
  , length parts >= 2  -- Has a comment
  , let expectation = Text.strip $ Text.concat $ drop 1 parts
  , not (Text.null expectation)
  ]

-- | Generic test case creation that runs a test and validates results
mkTestWithRunner :: (FilePath -> Text -> IO [Text]) -> FilePath -> FilePath -> IO TestTree
mkTestWithRunner runTest dir file = do
  let name = dropExtension file
      inputPath = dir </> file
  return $ testCase name $ do
    input <- TIO.readFile inputPath
    let expectations = parseExpectations input
    actualResults <- runTest inputPath input

    -- Assert that there are expectations
    if null expectations
      then assertFailure $ "No check-sat expectations found in " <> name <> ". All test files must have (check-sat) ; <expected-result> comments."
      else do
        -- Validate we got the expected number of results
        assertEqual
          ("Number of check-sat results in " <> name)
          (length expectations)
          (length actualResults)

        -- Validate each result matches expectation
        sequence_
          [ assertEqual
              (name <> ": check-sat #" <> show i <> " expected " <> Text.unpack expected)
              expected
              actual
          | (i, expected, actual) <- zip3 [1 :: Int ..] expectations actualResults
          ]

-- | Create a test case for a single SMT2 file using Who2
mkSimplTest :: FilePath -> FilePath -> IO TestTree
mkSimplTest = mkTestWithRunner $ \_inputPath input -> withIONonceGenerator $ \gen -> do
  let ?logStderr = \_ -> return ()
  builder <- newBuilder gen
  result <- solve builder input
  return [ case r of
             Sat _ -> "sat"
             Unsat _ -> "unsat"
             Unknown -> "unknown"
         | r <- erResults result
         ]

-- | Create a test case that runs z3 on a single SMT2 file
mkZ3ValidationTest :: FilePath -> FilePath -> IO TestTree
mkZ3ValidationTest = mkTestWithRunner $ \inputPath _input -> do
  result <- runZ3 inputPath
  case result of
    Left err -> assertFailure $ "z3 failed: " <> err
    Right z3Output -> return $ parseZ3Output z3Output
  where
    parseZ3Output :: Text -> [Text]
    parseZ3Output output =
      [ stripped
      | line <- Text.lines output
      , let stripped = Text.strip line
      , stripped `elem` ["sat", "unsat", "unknown"]
      ]

    runZ3 :: FilePath -> IO (Either String Text)
    runZ3 filePath = do
      result <- catch
        (do
          (exitCode, stdout, stderrOut) <- readProcessWithExitCode "z3" [filePath] ""
          case exitCode of
            ExitSuccess -> return $ Right $ Text.pack stdout
            _ -> return $ Left $ "z3 exited with error: " ++ stderrOut
        )
        (\(e :: SomeException) -> return $ Left $ "Exception running z3: " ++ show e)
      return result
