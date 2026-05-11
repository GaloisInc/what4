{-# LANGUAGE ImportQualifiedPost #-}

-- | Who2 test suite
--
-- As a foundation for verification tools, the correctness of Who2 is crucial.
-- We try hard to maintain fairly extensive tests.
--
-- For more information about each kind of test, see the corresponding modules:
--
-- Individual tests:
--
-- * "Who2.TestAnnotations"
-- * "Who2.Cryptol"
-- * "Who2.Functions"
-- * "Who2.SMTLib2"
-- * "Who2.Simplification"
--
-- Property tests:
--
-- * "Who2.Builder.API.GenTests"
-- * "Who2.Builder.Simplification"
-- * "Who2.Laws"
-- * "Who2.SemiRing"
-- * "Who2.Builder.Invariants"
module Main (main) where

import System.Directory (findExecutable)
import System.IO (hPutStrLn, stderr)
import Test.Tasty (defaultMain, testGroup)
import qualified Who2.Builder.API.GenTests as GenTests
import qualified Who2.Builder.Invariants as Invariants
import qualified Who2.Builder.Simplification as Props
import qualified Who2.Cryptol as Cryptol
import qualified Who2.Filter as Filter
import qualified Who2.Functions as Functions
import qualified Who2.Laws as Laws
import qualified Who2.SemiRing as SemiRing
import qualified Who2.Simplification as Simpl
import qualified Who2.SMTLib2 as SMTLib2
import qualified Who2.TestAnnotations as TestAnnotations

-- | Check if Z3 is available
checkZ3Available :: IO Bool
checkZ3Available = do
  result <- findExecutable "z3"
  case result of
    Just _ -> pure True
    Nothing -> do
      hPutStrLn stderr "WARNING: z3 not found in PATH. Semantic checks will be skipped."
      hPutStrLn stderr "Install z3 with: brew install z3 (macOS) or apt install z3 (Linux)"
      pure False

main :: IO ()
main = do
  z3Available <- checkZ3Available
  ioTests <-
    sequence $
      [ TestAnnotations.tests
      , Cryptol.tests
      , Functions.tests
      , SMTLib2.tests
      , Simpl.tests z3Available
      ]
  let pureTests =
        [ GenTests.tests
        , testGroup "Property Tests"
            [ Props.tests
            , Laws.tests
            , Filter.tests
            , SemiRing.tests
            , Invariants.tests
            ]
        ]

  defaultMain $ testGroup "Who2 Tests" (ioTests ++ pureTests)
