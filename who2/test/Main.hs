{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Control.Monad (unless)
import System.IO (hPutStrLn, stderr)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import qualified Hedgehog

import qualified Who2.Functions as Functions
import qualified Who2.HashedSeq as HashedSeq
import qualified Who2.Laws.Expr as LawsExpr
import qualified Who2.Laws.BloomSeq as LawsBloomSeq
import qualified Who2.Laws.BloomKv as LawsBloomKv
import qualified Who2.Laws.PolarizedBloomSeq as LawsPolarizedBloomSeq
import qualified Who2.Laws.HashedSeq as LawsHashedSeq
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
    , bloomKvEqByPropertyTests
    , bloomKvOrdByPropertyTests
    , polarizedBloomSeqEqByPropertyTests
    , polarizedBloomSeqOrdByPropertyTests
    , hashedSeqPropertyTests
    , hashedSeqOrdByPropertyTests
    ]

-- | Simplification correctness properties
simplificationCorrectnessTests :: TestTree
simplificationCorrectnessTests =
  testGroup "Simplification Correctness"
    [ testProperty "General simplifications (depth 5)" $
        Hedgehog.withTests 256 Props.propSimplificationCorrect
    , testProperty "Deep expressions (depth 10)" $
        Hedgehog.withTests 128 Props.propDeepSimplifications
    , testProperty "Singleton abstract domain iff literal" $
        Hedgehog.withTests 20000 Props.propSingletonAbstractDomainIffLiteral
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
        Hedgehog.withTests 1000 LawsExpr.propTestEqualityReflexive
    , testProperty "Symmetry (testEquality x y == testEquality y x)" $
        Hedgehog.withTests 1000 LawsExpr.propTestEqualitySymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsExpr.propTestEqualityTransitive
    , testProperty "Hash consistency (equal implies same hash)" $
        Hedgehog.withTests 1000 LawsExpr.propTestEqualityHashConsistent
    ]

-- | OrdF instance property tests
ordFPropertyTests :: TestTree
ordFPropertyTests =
  testGroup "OrdF Properties"
    [ testProperty "Reflexivity (compareF x x == EQF)" $
        Hedgehog.withTests 1000 LawsExpr.propOrdFReflexive
    , testProperty "Antisymmetry (compareF x y opposite of compareF y x)" $
        Hedgehog.withTests 1000 LawsExpr.propOrdFAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsExpr.propOrdFTransitive
    , testProperty "Consistency with TestEquality" $
        Hedgehog.withTests 1000 LawsExpr.propOrdFConsistentWithTestEquality
    ]

-- | Ord instance property tests
ordPropertyTests :: TestTree
ordPropertyTests =
  testGroup "Ord Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsExpr.propOrdReflexive
    , testProperty "Antisymmetry" $
        Hedgehog.withTests 1000 LawsExpr.propOrdAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsExpr.propOrdTransitive
    , testProperty "Consistency with Eq" $
        Hedgehog.withTests 1000 LawsExpr.propOrdConsistentWithEq
    ]

-- | BloomSeq eqBy property tests
bloomSeqEqByPropertyTests :: TestTree
bloomSeqEqByPropertyTests =
  testGroup "BloomSeq eqBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqEqByReflexive
    , testProperty "Symmetry" $
        Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqEqBySymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqEqByTransitive
    ]

-- | BloomSeq ordBy property tests
bloomSeqOrdByPropertyTests :: TestTree
bloomSeqOrdByPropertyTests =
  testGroup "BloomSeq ordBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByReflexive
    , testProperty "Antisymmetry" $
        Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByTransitive
    , testProperty "Consistency with eqBy" $
        Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByConsistentWithEqBy
    ]

-- | BloomKv eqBy property tests
bloomKvEqByPropertyTests :: TestTree
bloomKvEqByPropertyTests =
  testGroup "BloomKv eqBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsBloomKv.propBloomKvEqByReflexive
    , testProperty "Symmetry" $
        Hedgehog.withTests 1000 LawsBloomKv.propBloomKvEqBySymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsBloomKv.propBloomKvEqByTransitive
    ]

-- | BloomKv ordBy property tests
bloomKvOrdByPropertyTests :: TestTree
bloomKvOrdByPropertyTests =
  testGroup "BloomKv ordBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByReflexive
    , testProperty "Antisymmetry" $
        Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByTransitive
    , testProperty "Consistency with eqBy" $
        Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByConsistentWithEqBy
    ]

-- | PolarizedBloomSeq eqBy property tests
polarizedBloomSeqEqByPropertyTests :: TestTree
polarizedBloomSeqEqByPropertyTests =
  testGroup "PolarizedBloomSeq eqBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsPolarizedBloomSeq.propPolarizedBloomSeqEqByReflexive
    , testProperty "Symmetry" $
        Hedgehog.withTests 1000 LawsPolarizedBloomSeq.propPolarizedBloomSeqEqBySymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsPolarizedBloomSeq.propPolarizedBloomSeqEqByTransitive
    ]

-- | PolarizedBloomSeq ordBy property tests
polarizedBloomSeqOrdByPropertyTests :: TestTree
polarizedBloomSeqOrdByPropertyTests =
  testGroup "PolarizedBloomSeq ordBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsPolarizedBloomSeq.propPolarizedBloomSeqOrdByReflexive
    , testProperty "Antisymmetry" $
        Hedgehog.withTests 1000 LawsPolarizedBloomSeq.propPolarizedBloomSeqOrdByAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsPolarizedBloomSeq.propPolarizedBloomSeqOrdByTransitive
    , testProperty "Consistency with eqBy" $
        Hedgehog.withTests 1000 LawsPolarizedBloomSeq.propPolarizedBloomSeqOrdByConsistentWithEqBy
    ]

-- | HashedSeq property tests
hashedSeqPropertyTests :: TestTree
hashedSeqPropertyTests =
  testGroup "HashedSeq Properties"
    [ testProperty "Hash consistency (equal implies same hash)" $
        Hedgehog.withTests 1000 HashedSeq.propHashedSeqHashConsistency
    , testProperty "Eq consistency with list" $
        Hedgehog.withTests 1000 HashedSeq.propHashedSeqEqConsistency
    , testProperty "Append maintains hash consistency" $
        Hedgehog.withTests 1000 HashedSeq.propHashedSeqAppendHashConsistency
    , testProperty "Merge maintains hash consistency" $
        Hedgehog.withTests 1000 HashedSeq.propHashedSeqMergeHashConsistency
    ]

-- | HashedSeq ordBy property tests
hashedSeqOrdByPropertyTests :: TestTree
hashedSeqOrdByPropertyTests =
  testGroup "HashedSeq ordBy Properties"
    [ testProperty "Reflexivity" $
        Hedgehog.withTests 1000 LawsHashedSeq.propHashedSeqOrdByReflexive
    , testProperty "Antisymmetry" $
        Hedgehog.withTests 1000 LawsHashedSeq.propHashedSeqOrdByAntisymmetric
    , testProperty "Transitivity" $
        Hedgehog.withTests 1000 LawsHashedSeq.propHashedSeqOrdByTransitive
    ]
