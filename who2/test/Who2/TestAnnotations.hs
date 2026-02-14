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
import Test.Tasty.HUnit (testCase, assertFailure)

-- | Collect all test annotations from source files with given prefix
collectTestAnnotations :: String -> FilePath -> IO (Set String)
collectTestAnnotations prefix srcDir = do
  files <- findHaskellFiles srcDir
  annotations <- forM files $ \file -> do
    content <- readFile file
    return $ extractTestNames prefix content
  return $ Set.unions annotations

-- | Collect all property test names from test files
-- Looks for lines like: propFooBar :: Property
collectPropertyTests :: FilePath -> IO (Set String)
collectPropertyTests testDir = do
  files <- findHaskellFiles testDir
  props <- forM files $ \file -> do
    content <- readFile file
    return $ extractPropertyNames content
  return $ Set.unions props

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

-- | Extract test annotation names from file content with given prefix
-- Looks for lines like: -- test: foo or -- test-law: propFoo
extractTestNames :: String -> String -> Set String
extractTestNames prefix content =
  Set.fromList [name | line <- lines content, Just name <- [parseTestLine line]]
  where
    parseTestLine :: String -> Maybe String
    parseTestLine line =
      let trimmed = dropWhile (== ' ') line
          fullPrefix = "-- " ++ prefix ++ ": "
      in if fullPrefix `isPrefixOf` trimmed
         then Just $ drop (length fullPrefix) trimmed
         else Nothing

-- | Extract property test names from file content
-- Looks for lines like: propFooBar :: Property
extractPropertyNames :: String -> Set String
extractPropertyNames content =
  Set.fromList [name | line <- lines content, Just name <- [parsePropLine line]]
  where
    parsePropLine :: String -> Maybe String
    parsePropLine line =
      let trimmed = dropWhile (== ' ') line
      in if "prop" `isPrefixOf` trimmed && " :: Property" `isInfixOf` trimmed
         then Just $ takeWhile (/= ' ') trimmed
         else Nothing
    isInfixOf :: Eq a => [a] -> [a] -> Bool
    isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)
    tails :: [a] -> [[a]]
    tails [] = [[]]
    tails xs@(_:xs') = xs : tails xs'

-- | Collect all test file names from test-data/simpl directory
collectTestFiles :: FilePath -> IO (Set String)
collectTestFiles testDir = do
  files <- listDirectory testDir
  return $ Set.fromList [takeBaseName f | f <- files, takeExtension f == ".smt2"]

-- | Main test entry point
tests :: IO TestTree
tests = do
  let srcDir = "src"
      testDataDirSimpl = "test-data/simpl"
      testDataDirSMT2 = "test-data/smt2"
      lawsDir = "test/Who2/Laws"

  -- SMT2 simplification test annotations (uses "-- test:" prefix)
  smt2Annotations <- collectTestAnnotations "test" srcDir
  testFiles <- collectTestFiles testDataDirSimpl

  let smt2AnnotationsOnly = Set.difference smt2Annotations testFiles
      testFilesOnly = Set.difference testFiles smt2Annotations

  -- Property test annotations (uses "-- test-law:" prefix)
  propAnnotations <- collectTestAnnotations "test-law" $ srcDir </> "Who2"
  propTests <- collectPropertyTests lawsDir

  let annotationsOnly = Set.difference propAnnotations propTests
      propsOnly = Set.difference propTests propAnnotations

  -- SMT2 golden test annotations (uses "-- test-smt2:" prefix)
  smt2GoldenAnnotations <- collectTestAnnotations "test-smt2" srcDir
  smt2GoldenFiles <- collectTestFiles testDataDirSMT2

  let smt2GoldenAnnotationsOnly = Set.difference smt2GoldenAnnotations smt2GoldenFiles
      smt2GoldenFilesOnly = Set.difference smt2GoldenFiles smt2GoldenAnnotations

  return $ testGroup "Test Annotations"
    [ testGroup "SMT2 Simplification Tests"
        [ testCase "All test annotations have corresponding test files" $
            if Set.null smt2AnnotationsOnly
              then return ()
              else assertFailure $ unlines
                [ "Found test annotations without corresponding test files:"
                , unlines (map ("  - " ++) (sort $ Set.toList smt2AnnotationsOnly))
                ]

        , testCase "All test files have corresponding annotations" $
            if Set.null testFilesOnly
              then return ()
              else assertFailure $ unlines
                [ "Found test files without corresponding annotations in source:"
                , unlines (map ("  - " ++) (sort $ Set.toList testFilesOnly))
                ]
        ]

    , testGroup "Property Tests"
        [ testCase "All test-law annotations refer to actual property tests" $
            if Set.null annotationsOnly
              then return ()
              else assertFailure $ unlines
                [ "Found test-law annotations without corresponding property tests in test/Who2/Laws:"
                , unlines (map ("  - " ++) (sort $ Set.toList annotationsOnly))
                ]

        , testCase "All property tests are referenced by test-law annotations" $
            if Set.null propsOnly
              then return ()
              else assertFailure $ unlines
                [ "Found property tests without corresponding test-law annotations in src/:"
                , unlines (map ("  - " ++) (sort $ Set.toList propsOnly))
                ]
        ]

    , testGroup "SMT2 Golden Tests"
        [ testCase "All test-smt2 annotations have corresponding golden files" $
            if Set.null smt2GoldenAnnotationsOnly
              then return ()
              else assertFailure $ unlines
                [ "Found test-smt2 annotations without corresponding golden files:"
                , unlines (map ("  - " ++) (sort $ Set.toList smt2GoldenAnnotationsOnly))
                ]

        , testCase "All smt2 golden files have corresponding test-smt2 annotations" $
            if Set.null smt2GoldenFilesOnly
              then return ()
              else assertFailure $ unlines
                [ "Found test-data/smt2 golden files without corresponding test-smt2 annotations:"
                , unlines (map ("  - " ++) (sort $ Set.toList smt2GoldenFilesOnly))
                ]
        ]
    ]
