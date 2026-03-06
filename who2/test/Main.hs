{-# LANGUAGE ImportQualifiedPost #-}

-- | Who2 test suite
--
-- TODO
module Main (main) where

import System.Directory (findExecutable)
import System.IO (hPutStrLn, stderr)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, assertBool)

import Who2.Internal (assertionsEnabled)
import qualified Who2.Builder.API.GenTests as GenTests
import qualified Who2.Builder.Invariants as Invariants
import qualified Who2.Builder.Simplification as Props
import qualified Who2.Cryptol as Cryptol
import qualified Who2.Filter as Filter
import qualified Who2.Functions as Functions
import qualified Who2.Laws.Bloom.HashedSeq as LawsBloomHashedSeq
import qualified Who2.Laws.Bloom.Map as LawsBloomKv
import qualified Who2.Laws.Bloom.Polarized as LawsBloomPolarized
import qualified Who2.Laws.Bloom.SemiRing.Product as LawsBloomProduct
import qualified Who2.Laws.Bloom.SemiRing.Sum as LawsBloomSum
import qualified Who2.Laws.Bloom.Set as LawsBloomSeq
import qualified Who2.Laws.Expr as LawsExpr
import qualified Who2.Laws.HashConsed.Map as LawsExprMap
import qualified Who2.Laws.HashConsed.Polarized as LawsPolarizedExprSet
import qualified Who2.Laws.HashConsed.SemiRing.Product as LawsHCProduct
import qualified Who2.Laws.HashConsed.SemiRing.Sum as LawsHCSum
import qualified Who2.Laws.HashConsed.Set as LawsExprSet
import qualified Who2.SemiRing.Bloom.Product as SRBloomProduct
import qualified Who2.SemiRing.Bloom.Sum as SRBloomSum
import qualified Who2.SemiRing.HashConsed.Product as SRHCProduct
import qualified Who2.SemiRing.HashConsed.Sum as SRHCSum
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

z3ValidationTests :: Bool -> IO [TestTree]
z3ValidationTests z3Available =
  if z3Available
  then Simpl.discoverZ3ValidationTests "test-data/simpl"
  else return []

main :: IO ()
main = do
  z3Available <- checkZ3Available
  simplTests <- Simpl.discoverSimplificationTests "test-data/simpl"
  z3Tests <- z3ValidationTests z3Available
  smtLib2Tests <- SMTLib2.tests
  functionTests <- Functions.tests
  annotationTests <- TestAnnotations.tests
  cryptolTests <- Cryptol.tests

  defaultMain $ testGroup "Who2 Tests"
    [ -- See Note [Asserts] in who2
      testCase "assertions enabled" $ do
        assertsEnabled <- assertionsEnabled
        assertBool "assertions should be enabled" assertsEnabled
    , testGroup "SMT2 File Tests"
        [ testGroup "Simplification" simplTests
        , testGroup "Z3 Validation" z3Tests
        ]
    , smtLib2Tests
    , functionTests
    , testGroup "Property Tests"
        [ Props.tests
        , LawsExpr.tests
        , testGroup "Bloom Module Tests"
            [ LawsBloomSeq.tests
            , LawsBloomKv.tests
            , LawsBloomPolarized.tests
            , LawsBloomHashedSeq.tests
            , LawsBloomSum.tests
            , LawsBloomProduct.tests
            , Filter.tests
            ]
        , testGroup "HashConsed Module Tests"
            [ LawsExprSet.tests
            , LawsExprMap.tests
            , LawsPolarizedExprSet.tests
            , LawsHCSum.tests
            , LawsHCProduct.tests
            ]
        , testGroup "SemiRing Algebraic Laws"
            [ SRHCSum.tests
            , SRHCProduct.tests
            , SRBloomSum.tests
            , SRBloomProduct.tests
            ]
        , Invariants.tests
        ]
    , annotationTests
    , cryptolTests
    , GenTests.tests
    ]
