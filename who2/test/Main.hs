{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Control.Monad (unless)
import System.IO (hPutStrLn, stderr)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import qualified Hedgehog

import qualified Who2.Functions as Functions
import qualified Who2.Laws.Expr as LawsExpr
import qualified Who2.Laws.Bloom.Set as LawsBloomSeq
import qualified Who2.Laws.Bloom.Map as LawsBloomKv
import qualified Who2.Laws.Bloom.Polarized as LawsBloomPolarized
import qualified Who2.Laws.Bloom.HashedSeq as LawsBloomHashedSeq
import qualified Who2.Laws.Bloom.SemiRing.Sum as LawsBloomSum
import qualified Who2.Laws.Bloom.SemiRing.Product as LawsBloomProduct
import qualified Who2.Filter as Filter
import qualified Who2.Laws.HashConsed.Set as LawsExprSet
import qualified Who2.Laws.HashConsed.Map as LawsExprMap
import qualified Who2.Laws.HashConsed.Polarized as LawsPolarizedExprSet
import qualified Who2.Laws.HashConsed.SemiRing.Sum as LawsHCSum
import qualified Who2.Laws.HashConsed.SemiRing.Product as LawsHCProduct
import qualified Who2.SemiRing.HashConsed.Sum as SRHCSum
import qualified Who2.SemiRing.HashConsed.Product as SRHCProduct
import qualified Who2.SemiRing.Bloom.Sum as SRBloomSum
import qualified Who2.SemiRing.Bloom.Product as SRBloomProduct
import qualified Who2.Invariants as Invariants
import qualified Who2.Properties as Props
import qualified Who2.Simplification as Simpl
import qualified Who2.SMTLib2 as SMTLib2
import qualified Who2.TestAnnotations as TestAnnotations
import qualified Who2.Cryptol as Cryptol

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
  cryptolTests <- Cryptol.tests

  defaultMain $ testGroup "Who2 Tests"
    [ smt2FileTests simplTests z3Tests
    , propertyTests
    , smtLib2Tests
    , functionTests
    , annotationTests
    , cryptolTests
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
    , bloomTests
    , hashConsedTests
    , semiRingTests
    , invariantTests
    ]

-- | All Bloom module tests
bloomTests :: TestTree
bloomTests =
  testGroup "Bloom Module Tests"
    [ bloomSeqTests
    , bloomKvTests
    , bloomPolarizedTests
    , bloomHashedSeqTests
    , bloomSumTests
    , bloomProductTests
    , bloomFilterTests
    ]

-- | All HashConsed module tests
hashConsedTests :: TestTree
hashConsedTests =
  testGroup "HashConsed Module Tests"
    [ exprSetTests
    , exprMapTests
    , polarizedExprSetTests
    , hashConsedSumTests
    , hashConsedProductTests
    ]

-- | Simplification correctness properties
simplificationCorrectnessTests :: TestTree
simplificationCorrectnessTests =
  testGroup "Simplification Correctness"
    [ testProperty "General simplifications (depth 5)" $
        Hedgehog.withTests 32 Props.propSimplificationCorrect  -- TODO: increase
    , testProperty "Deep expressions (depth 10)" $
        Hedgehog.withTests 32 Props.propDeepSimplifications  -- TODO: increase
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
        Hedgehog.withTests 1000 $ Hedgehog.withDiscards 10000 LawsExpr.propTestEqualityHashConsistent
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

-- | Bloom.Seq tests
bloomSeqTests :: TestTree
bloomSeqTests =
  testGroup "Bloom.Seq"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsBloomSeq.propBloomSeqOrdByConsistentWithEqBy
        ]
    ]

-- | Bloom.Kv tests
bloomKvTests :: TestTree
bloomKvTests =
  testGroup "Bloom.Kv"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomKv.propBloomKvEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsBloomKv.propBloomKvEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomKv.propBloomKvEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsBloomKv.propBloomKvOrdByConsistentWithEqBy
        ]
    ]

-- | Bloom.Polarized tests
bloomPolarizedTests :: TestTree
bloomPolarizedTests =
  testGroup "Bloom.Polarized"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomPolarized.propPolarizedBloomSeqEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsBloomPolarized.propPolarizedBloomSeqEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomPolarized.propPolarizedBloomSeqEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomPolarized.propPolarizedBloomSeqOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsBloomPolarized.propPolarizedBloomSeqOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomPolarized.propPolarizedBloomSeqOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsBloomPolarized.propPolarizedBloomSeqOrdByConsistentWithEqBy
        ]
    ]

-- | Bloom.HashedSeq tests
bloomHashedSeqTests :: TestTree
bloomHashedSeqTests =
  testGroup "Bloom.HashedSeq"
    [ testGroup "Hash and Eq Properties"
        [ testProperty "Hash consistency (equal implies same hash)" $
            Hedgehog.withTests 1000 LawsBloomHashedSeq.propHashedSeqHashConsistency
        , testProperty "Eq consistency with list" $
            Hedgehog.withTests 1000 LawsBloomHashedSeq.propHashedSeqEqConsistency
        , testProperty "Append maintains hash consistency" $
            Hedgehog.withTests 1000 LawsBloomHashedSeq.propHashedSeqAppendHashConsistency
        , testProperty "Merge maintains hash consistency" $
            Hedgehog.withTests 1000 LawsBloomHashedSeq.propHashedSeqMergeHashConsistency
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomHashedSeq.propHashedSeqOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsBloomHashedSeq.propHashedSeqOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomHashedSeq.propHashedSeqOrdByTransitive
        ]
    ]

-- | Bloom.Sum tests
bloomSumTests :: TestTree
bloomSumTests =
  testGroup "Bloom.Sum"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomSum.propBloomSumEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsBloomSum.propBloomSumEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomSum.propBloomSumEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomSum.propBloomSumOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsBloomSum.propBloomSumOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomSum.propBloomSumOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsBloomSum.propBloomSumOrdByConsistentWithEqBy
        ]
    ]

-- | Bloom.Product tests
bloomProductTests :: TestTree
bloomProductTests =
  testGroup "Bloom.Product"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomProduct.propBloomProductEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsBloomProduct.propBloomProductEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomProduct.propBloomProductEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsBloomProduct.propBloomProductOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsBloomProduct.propBloomProductOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsBloomProduct.propBloomProductOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsBloomProduct.propBloomProductOrdByConsistentWithEqBy
        ]
    ]

-- | Bloom.Filter tests
bloomFilterTests :: TestTree
bloomFilterTests =
  testGroup "Bloom.Filter"
    [ testProperty "Empty filter might not contain" $
        Hedgehog.withTests 1000 Filter.propFilterEmptyMightNotContain
    , testProperty "Insert makes mightContain true" $
        Hedgehog.withTests 1000 Filter.propFilterInsertMightContain
    , testProperty "Empty filters are disjoint" $
        Hedgehog.withTests 1000 Filter.propFilterDisjointEmpty
    , testProperty "Union contains both elements" $
        Hedgehog.withTests 1000 Filter.propFilterUnionContains
    ]

-- | HashConsed.ExprSet tests
exprSetTests :: TestTree
exprSetTests =
  testGroup "HashConsed.ExprSet"
    [ testGroup "Eq Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsExprSet.propExprSetEqReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsExprSet.propExprSetEqSymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsExprSet.propExprSetEqTransitive
        ]
    , testGroup "Ord Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsExprSet.propExprSetOrdReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsExprSet.propExprSetOrdAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsExprSet.propExprSetOrdTransitive
        , testProperty "Consistency with Eq" $
            Hedgehog.withTests 1000 LawsExprSet.propExprSetOrdConsistentWithEq
        ]
    ]

-- | HashConsed.ExprMap tests
exprMapTests :: TestTree
exprMapTests =
  testGroup "HashConsed.ExprMap"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsExprMap.propExprMapEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsExprMap.propExprMapEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsExprMap.propExprMapEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsExprMap.propExprMapOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsExprMap.propExprMapOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsExprMap.propExprMapOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsExprMap.propExprMapOrdByConsistentWithEqBy
        ]
    ]

-- | HashConsed.PolarizedExprSet tests
polarizedExprSetTests :: TestTree
polarizedExprSetTests =
  testGroup "HashConsed.PolarizedExprSet"
    [ testProperty "Eq/Hash consistency (equal implies same hash)" $
        Hedgehog.withTests 1000 $ Hedgehog.withDiscards 10000 LawsPolarizedExprSet.propPolarizedExprSetEqHashConsistency
    ]

-- | HashConsed.SemiRing.Sum tests
hashConsedSumTests :: TestTree
hashConsedSumTests =
  testGroup "HashConsed.SemiRing.Sum"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsHCSum.propHashConsedSumEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsHCSum.propHashConsedSumEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsHCSum.propHashConsedSumEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsHCSum.propHashConsedSumOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsHCSum.propHashConsedSumOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsHCSum.propHashConsedSumOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsHCSum.propHashConsedSumOrdByConsistentWithEqBy
        ]
    ]

-- | HashConsed.SemiRing.Product tests
hashConsedProductTests :: TestTree
hashConsedProductTests =
  testGroup "HashConsed.SemiRing.Product"
    [ testGroup "eqBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsHCProduct.propHashConsedProductEqByReflexive
        , testProperty "Symmetry" $
            Hedgehog.withTests 1000 LawsHCProduct.propHashConsedProductEqBySymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsHCProduct.propHashConsedProductEqByTransitive
        ]
    , testGroup "ordBy Properties"
        [ testProperty "Reflexivity" $
            Hedgehog.withTests 1000 LawsHCProduct.propHashConsedProductOrdByReflexive
        , testProperty "Antisymmetry" $
            Hedgehog.withTests 1000 LawsHCProduct.propHashConsedProductOrdByAntisymmetric
        , testProperty "Transitivity" $
            Hedgehog.withTests 1000 LawsHCProduct.propHashConsedProductOrdByTransitive
        , testProperty "Consistency with eqBy" $
            Hedgehog.withTests 1000 LawsHCProduct.propHashConsedProductOrdByConsistentWithEqBy
        ]
    ]

-- | SemiRing algebraic law tests
semiRingTests :: TestTree
semiRingTests =
  testGroup "SemiRing Algebraic Laws"
    [ hashConsedSemiRingTests
    , bloomSemiRingTests
    ]

-- | HashConsed SemiRing tests
hashConsedSemiRingTests :: TestTree
hashConsedSemiRingTests =
  testGroup "HashConsed SemiRing"
    [ testGroup "Sum"
        [ testProperty "Addition Associativity" $
            Hedgehog.withTests 1000 SRHCSum.propHashConsedSumAddAssociative
        , testProperty "Addition Commutativity" $
            Hedgehog.withTests 1000 SRHCSum.propHashConsedSumAddCommutative
        , testProperty "Addition Identity" $
            Hedgehog.withTests 1000 SRHCSum.propHashConsedSumAddIdentity
        , testProperty "AddConstant Associativity" $
            Hedgehog.withTests 1000 SRHCSum.propHashConsedSumAddConstantAssociative
        , testProperty "Scalar Distributivity" $
            Hedgehog.withTests 1000 SRHCSum.propHashConsedSumScalarDistributivity
        , testProperty "Coefficient Cancellation" $
            Hedgehog.withTests 1000 SRHCSum.propHashConsedSumCancellation
        ]
    , testGroup "Product"
        [ testProperty "Multiplication Associativity" $
            Hedgehog.withTests 1000 SRHCProduct.propHashConsedProductMulAssociative
        , testProperty "Multiplication Identity" $
            Hedgehog.withTests 1000 SRHCProduct.propHashConsedProductMulIdentity
        , testProperty "Scale Associativity" $
            Hedgehog.withTests 1000 SRHCProduct.propHashConsedProductScaleAssociative
        , testProperty "Scale Distributes Over Multiplication" $
            Hedgehog.withTests 1000 SRHCProduct.propHashConsedProductScaleDistributesOverMul
        ]
    ]

-- | Bloom SemiRing tests
bloomSemiRingTests :: TestTree
bloomSemiRingTests =
  testGroup "Bloom SemiRing"
    [ testGroup "Sum"
        [ testProperty "Addition Associativity (below threshold)" $
            Hedgehog.withTests 1000 SRBloomSum.propBloomSumAddAssociative
        , testProperty "Addition Identity (below threshold)" $
            Hedgehog.withTests 1000 SRBloomSum.propBloomSumAddIdentity
        , testProperty "AddConstant Associativity (below threshold)" $
            Hedgehog.withTests 1000 SRBloomSum.propBloomSumAddConstantAssociative
        , testProperty "Scalar Distributivity (below threshold)" $
            Hedgehog.withTests 1000 SRBloomSum.propBloomSumScalarDistributivity
        , testProperty "Coefficient Cancellation" $
            Hedgehog.withTests 1000 SRBloomSum.propBloomSumCancellation
        ]
    , testGroup "Product"
        [ testProperty "Multiplication Associativity (below threshold)" $
            Hedgehog.withTests 1000 SRBloomProduct.propBloomProductMulAssociative
        , testProperty "Multiplication Identity (below threshold)" $
            Hedgehog.withTests 1000 SRBloomProduct.propBloomProductMulIdentity
        , testProperty "Scale Associativity (below threshold)" $
            Hedgehog.withTests 1000 SRBloomProduct.propBloomProductScaleAssociative
        , testProperty "Scale Distributes Over Multiplication (below threshold)" $
            Hedgehog.withTests 1000 SRBloomProduct.propBloomProductScaleDistributesOverMul
        ]
    ]

-- | AST Invariant tests
invariantTests :: TestTree
invariantTests =
  testGroup "AST Invariants"
    [ testProperty "No empty or singleton structures (Bool)" $
        Hedgehog.withTests 1000 Invariants.propNoEmptyOrSingletonStructures
    , testProperty "No empty or singleton structures (BV)" $
        Hedgehog.withTests 1000 Invariants.propNoEmptyOrSingletonStructuresBV
    ]
