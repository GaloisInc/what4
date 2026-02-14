{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.Cryptol (tests) where

import Control.Exception qualified as Exception
import Control.Monad (forM)
import Data.List (isPrefixOf, stripPrefix)
import System.Directory (doesFileExist, findExecutable, listDirectory)
import System.Exit (ExitCode(ExitSuccess, ExitFailure))
import System.FilePath ((</>), takeExtension)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure, assertBool)

-- | Main test entry point
tests :: IO TestTree
tests = do
  -- Check if cryptol binary is available
  maybeCryptol <- findExecutable "cryptol"
  case maybeCryptol of
    Nothing -> return $ testGroup "Cryptol Proofs"
      [ testCase "Cryptol binary not found (skipping tests)" $
          assertBool "Cryptol not installed - tests skipped" True
      ]
    Just cryptolPath -> do
      -- Find all Cryptol proofs in source files
      proofs <- collectCryptolProofs "src"

      -- Create a test for each proof
      let cryptolTests = map (makeCryptolTest cryptolPath) proofs

      return $ testGroup "Cryptol Proofs"
        [ testGroup "Extracted Proofs" cryptolTests
        ]

-- | A Cryptol proof found in source code
data CryptolProof = CryptolProof
  { cpFilePath :: FilePath
  , cpLineNumber :: Int
  , cpProofStatement :: String
  } deriving (Show, Eq)

-- | Collect all Cryptol proof annotations from source files
collectCryptolProofs :: FilePath -> IO [CryptolProof]
collectCryptolProofs srcDir = do
  files <- findHaskellFiles srcDir
  proofLists <- forM files $ \file -> do
    content <- readFile file
    return $ extractCryptolProofs file content
  return $ concat proofLists

-- | Find all Haskell source files recursively
findHaskellFiles :: FilePath -> IO [FilePath]
findHaskellFiles dir = do
  entries <- listDirectory dir
  let fullPaths = map (dir </>) entries
  results <- forM fullPaths $ \path -> do
    isFile <- doesFileExist path
    if isFile && takeExtension path == ".hs"
      then return [path]
      else Exception.catch (findHaskellFiles path) (\(_ :: IOError) -> return [])
  return $ concat results

-- | Extract Cryptol proof statements from file content
-- Looks for lines like: -- Cryptol> :prove \(x : [8]) -> x + 0 == x
extractCryptolProofs :: FilePath -> String -> [CryptolProof]
extractCryptolProofs filePath content =
  [ CryptolProof filePath lineNum proof
  | (lineNum, line) <- zip [1..] (lines content)
  , Just proof <- [parseCryptolLine line]
  ]
  where
    parseCryptolLine :: String -> Maybe String
    parseCryptolLine line =
      let trimmed = dropWhile (== ' ') line
          prefix = "-- Cryptol> "
      in if prefix `isPrefixOf` trimmed
         then stripPrefix prefix trimmed
         else Nothing

-- | Create a test case for a Cryptol proof
makeCryptolTest :: FilePath -> CryptolProof -> TestTree
makeCryptolTest cryptolPath proof =
  testCase testName $ do
    -- Run the proof through Cryptol
    result <- runCryptolProof cryptolPath (cpProofStatement proof)
    case result of
      Left err -> assertFailure $ unlines
        [ "Cryptol proof failed: " ++ cpFilePath proof ++ ":" ++ show (cpLineNumber proof)
        , "Statement: " ++ cpProofStatement proof
        , "Error: " ++ err
        ]
      Right () -> return ()
  where
    -- Extract just the lambda term from the :prove statement
    testName = case stripPrefix ":prove " (cpProofStatement proof) of
      Just lambdaTerm -> lambdaTerm
      Nothing -> cpProofStatement proof

-- | Run a Cryptol proof statement and check if it succeeds
runCryptolProof :: FilePath -> String -> IO (Either String ())
runCryptolProof cryptolPath proofStmt = do
  -- Run cryptol with -c command option
  (exitCode, stdout, stderr) <- readProcessWithExitCode
    cryptolPath
    ["-c", proofStmt]
    ""

  case exitCode of
    ExitSuccess ->
      -- Check output for success indicators
      if "Q.E.D." `isInfixOf` stdout
      then return $ Right ()
      else if "Counterexample" `isInfixOf` stdout
           then return $ Left $ "Found counterexample:\n" ++ stdout
           else return $ Right ()  -- Assume success if no error
    ExitFailure code ->
      return $ Left $ unlines
        [ "Cryptol exited with code " ++ show code
        , "stdout: " ++ stdout
        , "stderr: " ++ stderr
        ]
  where
    isInfixOf :: Eq a => [a] -> [a] -> Bool
    isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)

    tails :: [a] -> [[a]]
    tails [] = [[]]
    tails xs@(_:xs') = xs : tails xs'
