{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module WeightedSum (weightedSumTests) where

import Data.Hashable (Hashable(..))
import qualified Data.BitVector.Sized as BV
import Data.Maybe (isNothing)
import Data.Parameterized.Classes
import GHC.TypeNats ()

import Data.Foldable (foldl1)

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog.Alt

import What4.BaseTypes
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.SemiRing as SR
import qualified What4.Utils.AbstractDomains as AD

-------------------------------------------------------------------------------
-- Mock Expression Type
-------------------------------------------------------------------------------

-- | Mock expression type for testing WeightedSum without a full ExprBuilder
data MockExpr (tp :: BaseType) = MockExpr Int (BaseTypeRepr tp)
  deriving (Show)

instance Eq (MockExpr tp) where
  MockExpr i _ == MockExpr j _ = i == j

instance Ord (MockExpr tp) where
  compare (MockExpr i _) (MockExpr j _) = compare i j

instance Hashable (MockExpr tp) where
  hashWithSalt s (MockExpr i _) = s `hashWithSalt` i

instance TestEquality MockExpr where
  testEquality (MockExpr i repr1) (MockExpr j repr2)
    | i == j = testEquality repr1 repr2
    | otherwise = Nothing

instance OrdF MockExpr where
  compareF (MockExpr i repr1) (MockExpr j repr2) =
    case compare i j of
      LT -> LTF
      GT -> GTF
      EQ -> case compareF repr1 repr2 of
        LTF -> LTF
        GTF -> GTF
        EQF -> EQF

instance HashableF MockExpr where
  hashWithSaltF s (MockExpr i _) = s `hashWithSalt` i

instance AD.HasAbsValue MockExpr where
  getAbsValue (MockExpr _ repr) = AD.avTop repr

-------------------------------------------------------------------------------
-- Generators
-------------------------------------------------------------------------------

genMockExpr :: KnownRepr BaseTypeRepr tp => Gen (MockExpr tp)
genMockExpr = MockExpr <$> Gen.int (Range.linear 0 100) <*> pure knownRepr

genBV8Constant :: Gen (BV.BV 8)
genBV8Constant = BV.mkBV knownNat . fromIntegral <$> Gen.int (Range.linear 0 255)

genWeightedSumBV8 :: Gen (WSum.WeightedSum MockExpr (SR.SemiRingBV SR.BVArith 8))
genWeightedSumBV8 = do
  offset <- genBV8Constant
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- genMockExpr @(BaseBVType 8)
    coeff <- genBV8Constant
    pure (key, coeff)
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  pure $ WSum.fromTerms sr terms offset

-- Generator for products
genProductBV8 :: Gen (WSum.SemiRingProduct MockExpr (SR.SemiRingBV SR.BVBits 8))
genProductBV8 = do
  numTerms <- Gen.int (Range.linear 1 3)
  terms <- Gen.list (Range.singleton numTerms) $ genMockExpr @(BaseBVType 8)
  let sr = SR.SemiRingBVRepr SR.BVBitsRepr (knownNat @8)
  pure $ foldl1 WSum.prodMul (map (WSum.prodVar sr) terms)

-------------------------------------------------------------------------------
-- Properties
-------------------------------------------------------------------------------

-- | Test that addition is associative: (a + b) + c == a + (b + c)
propAddAssociative :: Property
propAddAssociative = property $ do
  s1 <- forAllWith (const "WeightedSum") genWeightedSumBV8
  s2 <- forAllWith (const "WeightedSum") genWeightedSumBV8
  s3 <- forAllWith (const "WeightedSum") genWeightedSumBV8
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  let lhs = WSum.add sr (WSum.add sr s1 s2) s3
  let rhs = WSum.add sr s1 (WSum.add sr s2 s3)
  assert $ lhs == rhs

-- | Test that zero is the additive identity: s + 0 == s
propAddIdentity :: Property
propAddIdentity = property $ do
  s <- forAllWith (const "WeightedSum") genWeightedSumBV8
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  let zero = WSum.constant sr (SR.zero sr)
  let result = WSum.add sr s zero
  assert $ result == s

-- | Test that adding constants is associative: (s + c1) + c2 == s + (c1 + c2)
propAddConstantAssociative :: Property
propAddConstantAssociative = property $ do
  s <- forAllWith (const "WeightedSum") genWeightedSumBV8
  c1 <- forAll genBV8Constant
  c2 <- forAll genBV8Constant
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  let lhs = WSum.addConstant sr (WSum.addConstant sr s c1) c2
  let rhs = WSum.addConstant sr s (SR.add sr c1 c2)
  assert $ lhs == rhs

-- | Test scalar multiplication distributivity: (c1 + c2) * x == c1*x + c2*x
propScalarDistributivity :: Property
propScalarDistributivity = property $ do
  c1 <- forAll genBV8Constant
  c2 <- forAll genBV8Constant
  x <- forAll (genMockExpr @(BaseBVType 8))
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  let lhs = WSum.scaledVar sr (SR.add sr c1 c2) x
  let rhs = WSum.add sr (WSum.scaledVar sr c1 x) (WSum.scaledVar sr c2 x)
  assert $ lhs == rhs

-- | Test that scaling is associative: scale c2 (scale c1 s) == scale (c1*c2) s
propScaleAssociative :: Property
propScaleAssociative = property $ do
  s <- forAllWith (const "WeightedSum") genWeightedSumBV8
  c1 <- forAll genBV8Constant
  c2 <- forAll genBV8Constant
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  let lhs = WSum.scale sr c2 (WSum.scale sr c1 s)
  let rhs = WSum.scale sr (SR.mul sr c1 c2) s
  assert $ lhs == rhs

-- | Test that scaling distributes over addition: c * (s1 + s2) == c*s1 + c*s2
propScaleDistributesOverAdd :: Property
propScaleDistributesOverAdd = property $ do
  s1 <- forAllWith (const "WeightedSum") genWeightedSumBV8
  s2 <- forAllWith (const "WeightedSum") genWeightedSumBV8
  c <- forAll genBV8Constant
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  let lhs = WSum.scale sr c (WSum.add sr s1 s2)
  let rhs = WSum.add sr (WSum.scale sr c s1) (WSum.scale sr c s2)
  assert $ lhs == rhs

-- | Test cancellation: adding opposite scalars cancels out
propCancellation :: Property
propCancellation = property $ do
  c <- forAll genBV8Constant
  x <- forAll (genMockExpr @(BaseBVType 8))
  let sr = SR.SemiRingBVRepr SR.BVArithRepr (knownNat @8)
  let negC = BV.negate (knownNat @8) c
  let result = WSum.add sr (WSum.scaledVar sr c x) (WSum.scaledVar sr negC x)
  -- After cancellation, should be just the constant (no variable terms)
  assert $ isNothing (WSum.asVar result)

-------------------------------------------------------------------------------
-- Product Properties
-------------------------------------------------------------------------------

-- | Test that multiplication is associative: (a * b) * c == a * (b * c)
propMulAssociative :: Property
propMulAssociative = property $ do
  p1 <- forAllWith (const "Product") genProductBV8
  p2 <- forAllWith (const "Product") genProductBV8
  p3 <- forAllWith (const "Product") genProductBV8
  let lhs = WSum.prodMul (WSum.prodMul p1 p2) p3
  let rhs = WSum.prodMul p1 (WSum.prodMul p2 p3)
  assert $ lhs == rhs

-- | Test that multiplication is commutative: a * b == b * a
propMulCommutative :: Property
propMulCommutative = property $ do
  p1 <- forAllWith (const "Product") genProductBV8
  p2 <- forAllWith (const "Product") genProductBV8
  let lhs = WSum.prodMul p1 p2
  let rhs = WSum.prodMul p2 p1
  assert $ lhs == rhs

-- | Test that single variable product is idempotent: var x * var x == var x
-- (in the BVBits semiring, which is idempotent)
propProdVarIdempotent :: Property
propProdVarIdempotent = property $ do
  x <- forAll (genMockExpr @(BaseBVType 8))
  let sr = SR.SemiRingBVRepr SR.BVBitsRepr (knownNat @8)
  let var_x = WSum.prodVar sr x
  let result = WSum.prodMul var_x var_x
  assert $ result == var_x

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

weightedSumTests :: TestTree
weightedSumTests = testGroup "WeightedSum and SemiRingProduct"
  [ testGroup "WeightedSum (Sums)"
      [ testProperty "Addition is associative" $
          withTests 2048 propAddAssociative
      , testProperty "Zero is additive identity" $
          withTests 2048 propAddIdentity
      , testProperty "Adding constants is associative" $
          withTests 2048 propAddConstantAssociative
      , testProperty "Scalar multiplication distributes" $
          withTests 2048 propScalarDistributivity
      , testProperty "Scaling is associative" $
          withTests 2048 propScaleAssociative
      , testProperty "Scaling distributes over addition" $
          withTests 2048 propScaleDistributesOverAdd
      , testProperty "Adding opposite scalars cancels" $
          withTests 2048 propCancellation
      ]
  , testGroup "SemiRingProduct (Products)"
      [ testProperty "Multiplication is associative" $
          withTests 2048 propMulAssociative
      , testProperty "Multiplication is commutative" $
          withTests 2048 propMulCommutative
      , testProperty "Product variable is idempotent (BVBits)" $
          withTests 2048 propProdVarIdempotent
      ]
  ]
