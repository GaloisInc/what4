{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.TestAnnotations (tests) where

import Control.Exception qualified
import Control.Monad (forM)
import Data.List (isPrefixOf, sort)
import Data.Set (Set)
import Data.Set qualified as Set
import System.Directory (doesFileExist, listDirectory)
import System.FilePath ((</>), takeExtension, takeBaseName)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure)

-- | Collect all test names from source files
collectTestAnnotations :: FilePath -> IO (Set String)
collectTestAnnotations srcDir = do
  files <- findHaskellFiles srcDir
  annotations <- forM files $ \file -> do
    content <- readFile file
    return $ extractTestNames content
  return $ Set.unions annotations

-- | Find all Haskell source files recursively
findHaskellFiles :: FilePath -> IO [FilePath]
findHaskellFiles dir = do
  entries <- listDirectory dir
  let fullPaths = map (dir </>) entries
  results <- forM fullPaths $ \path -> do
    isFile <- doesFileExist path
    if isFile && takeExtension path == ".hs"
      then return [path]
      else Control.Exception.catch (findHaskellFiles path) (\(_ :: IOError) -> return [])
  return $ concat results

-- | Extract test names from file content
-- Looks for lines like: -- test: test-name
extractTestNames :: String -> Set String
extractTestNames content =
  Set.fromList [name | line <- lines content, Just name <- [parseTestLine line]]
  where
    parseTestLine :: String -> Maybe String
    parseTestLine line =
      let trimmed = dropWhile (== ' ') line
      in if "-- test: " `isPrefixOf` trimmed
         then Just $ drop (length "-- test: ") trimmed
         else Nothing

-- | Collect all test file names from test-data/simpl directory
collectTestFiles :: FilePath -> IO (Set String)
collectTestFiles testDir = do
  files <- listDirectory testDir
  return $ Set.fromList [takeBaseName f | f <- files, takeExtension f == ".smt2"]

-- | Main test entry point
tests :: IO TestTree
tests = do
  let srcDir = "src"
      testDataDir = "test-data/simpl"

  annotations <- collectTestAnnotations srcDir
  testFiles <- collectTestFiles testDataDir

  let annotationsOnly = Set.difference annotations testFiles
      testFilesOnly = Set.difference testFiles annotations

  return $ testGroup "Test Annotations"
    [ testCase "All test annotations have corresponding test files" $
        if Set.null annotationsOnly
          then return ()
          else assertFailure $ unlines
            [ "Found test annotations without corresponding test files:"
            , unlines (map ("  - " ++) (sort $ Set.toList annotationsOnly))
            ]

    , testCase "All test files have corresponding annotations" $
        if Set.null testFilesOnly
          then return ()
          else assertFailure $ unlines
            [ "Found test files without corresponding annotations in source:"
            , unlines (map ("  - " ++) (sort $ Set.toList testFilesOnly))
            ]

    , testCase "Test annotation count" $
        assertBool ("Should have test annotations, found " ++ show (Set.size annotations))
          (Set.size annotations > 0)
    ]
