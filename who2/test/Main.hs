{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Control.Monad (unless)
import System.IO (hPutStrLn, stderr)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import qualified Hedgehog

import qualified Who2.Functions as Functions
import qualified Who2.Instances as Instances
import qualified Who2.Properties as Props
import qualified Who2.Simplification as Simpl
import qualified Who2.SMTLib2 as SMTLib2
import qualified Who2.TestAnnotations as TestAnnotations

main :: IO ()
main = do
  -- Check if z3 is available
  z3Available <- Props.checkZ3Available
  unless z3Available $ do
    hPutStrLn stderr "WARNING: z3 not found in PATH. Semantic checks will be skipped."
    hPutStrLn stderr "Install z3 with: brew install z3 (macOS) or apt install z3 (Linux)"

  -- Discover SMT2 file tests
  simplTests <- Simpl.discoverSimplificationTests "test-data/simpl"

  z3Tests <- if z3Available
    then Simpl.discoverZ3ValidationTests "test-data/simpl"
    else do
      putStrLn "Warning: z3 not found in PATH. Skipping z3 validation tests."
      return []

  smtLib2Tests <- SMTLib2.tests
  functionTests <- Functions.tests
  annotationTests <- TestAnnotations.tests

  defaultMain $ testGroup "Who2 Tests"
    [ smt2FileTests simplTests z3Tests
    , propertyTests
    , smtLib2Tests
    , functionTests
    , annotationTests
    ]

-- | SMT2 file-based tests
smt2FileTests :: [TestTree] -> [TestTree] -> TestTree
smt2FileTests simplTests z3Tests =
  testGroup "SMT2 File Tests"
    [ testGroup "Simplification" simplTests
    , testGroup "Z3 Validation" z3Tests
    ]

-- | Property-based tests
propertyTests :: TestTree
propertyTests =
  testGroup "Property Tests"
    [ simplificationCorrectnessTests
    , typeSpecificPropertyTests
    , testEqualityPropertyTests
    , ordFPropertyTests
    , ordPropertyTests
    , bloomSeqEqByPropertyTests
    , bloomSeqOrdByPropertyTests
    ]

-- | Simplification correctness properties
simplificationCorrectnessTests :: TestTree
simplificationCorrectnessTests =
  testGroup "Simplification Correctness"
    [ testProperty "General simplifications (depth 5)" $
        Hedgehog.withTests 256 Props.propSimplificationCorrect
    , testProperty "Deep expressions (depth 10)" $
        Hedgehog.withTests 128 Props.propDeepSimplifications
    ]

-- | Type-specific property tests
typeSpecificPropertyTests :: TestTree
typeSpecificPropertyTests =
  testGroup "Type-Specific Properties"
    [ testProperty "Boolean-only expressions (100 tests)" $
        Hedgehog.withTests 128 Props.propBoolSimplifications
    , testProperty "BV arithmetic expressions (100 tests)" $
        Hedgehog.withTests 128 Props.propBvArithSimplifications
    ]

-- | TestEquality instance property tests
testEqualityPropertyTests :: TestTree
testEqualityPropertyTests =
  testGroup "TestEquality Properties"
    [ testProperty "Reflexivity (testEquality x x == Just Refl)" $
        Hedgehog.withTests 1000 Instances.propTestEqualityReflexive
    , testProperty "Symmetry (testEquality x y == testEquality y x)" $
        Hedgehog.withTests 1000 Instances.propTestEqualitySymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 Instances.propTestEqualityTransitive
    , testProperty "Hash consistency (equal implies same hash)" $
        Hedgehog.withTests 1000 Instances.propTestEqualityHashConsistent
    ]

-- | OrdF instance property tests
ordFPropertyTests :: TestTree
ordFPropertyTests =
  testGroup "OrdF Properties"
    [ testProperty "Reflexivity (compareF x x == EQF)" $
        Hedgehog.withTests 1000 Instances.propOrdFReflexive
    , testProperty "Antisymmetry (compareF x y opposite of compareF y x)" $
        Hedgehog.withTests 1000 Instances.propOrdFAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 Instances.propOrdFTransitive
    , testProperty "Consistency with TestEquality" $
        Hedgehog.withTests 1000 Instances.propOrdFConsistentWithTestEquality
    ]

-- | Ord instance property tests
ordPropertyTests :: TestTree
ordPropertyTests =
  testGroup "Ord Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 Instances.propOrdReflexive
    , testProperty "Antisymmetry" $
        Hedgehog.withTests 1000 Instances.propOrdAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 Instances.propOrdTransitive
    , testProperty "Consistency with Eq" $
        Hedgehog.withTests 1000 Instances.propOrdConsistentWithEq
    ]

-- | BloomSeq eqBy property tests
bloomSeqEqByPropertyTests :: TestTree
bloomSeqEqByPropertyTests =
  testGroup "BloomSeq eqBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 Instances.propBloomSeqEqByReflexive
    , testProperty "Symmetry" $
        Hedgehog.withTests 1000 Instances.propBloomSeqEqBySymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 Instances.propBloomSeqEqByTransitive
    ]

-- | BloomSeq ordBy property tests
bloomSeqOrdByPropertyTests :: TestTree
bloomSeqOrdByPropertyTests =
  testGroup "BloomSeq ordBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 Instances.propBloomSeqOrdByReflexive
    , testProperty "Antisymmetry" $
        Hedgehog.withTests 1000 Instances.propBloomSeqOrdByAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 Instances.propBloomSeqOrdByTransitive
    , testProperty "Consistency with eqBy" $
        Hedgehog.withTests 1000 Instances.propBloomSeqOrdByConsistentWithEqBy
    ]
