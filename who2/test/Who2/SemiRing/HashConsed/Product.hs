{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

module Who2.SemiRing.HashConsed.Product (tests) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Data.BitVector.Sized as BV
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.Parameterized.NatRepr (knownNat)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified What4.BaseTypes as BT
import qualified What4.SemiRing as SR

import qualified Who2.Expr.HashConsed.SemiRing.Product as HCPR
import Who2.Laws.Helpers (MockExprBT(..), genMockExprBT)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genHashConsedProductBV8 :: H.Gen (HCPR.SRProd (SR.SemiRingBV SR.BVBits 8) MockExprBT)
genHashConsedProductBV8 = do
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- genMockExprBT @(BT.BaseBVType 8)
    expnt <- Gen.integral (Range.linear 1 5)
    pure (key, expnt)
  pure $ HCPR.fromTerms (SR.SemiRingBVRepr SR.BVBitsRepr knownNat) terms

genBV8Coeff :: H.Gen (BV.BV 8)
genBV8Coeff = BV.mkBV knownNat . fromIntegral <$> Gen.int (Range.linear 0 255)

-------------------------------------------------------------------------------
-- HashConsed Product Properties
-------------------------------------------------------------------------------

propHashConsedProductMulAssociative :: Property
propHashConsedProductMulAssociative = H.property $ do
  p1 <- H.forAll genHashConsedProductBV8
  p2 <- H.forAll genHashConsedProductBV8
  p3 <- H.forAll genHashConsedProductBV8
  let lhs = HCPR.mul (HCPR.mul p1 p2) p3
  let rhs = HCPR.mul p1 (HCPR.mul p2 p3)
  lhs H.=== rhs

propHashConsedProductMulIdentity :: Property
propHashConsedProductMulIdentity = H.property $ do
  p <- H.forAll genHashConsedProductBV8
  let sr = HCPR.prodRepr p
  let one = HCPR.one sr
  let result = HCPR.mul p one
  unless (HCPR.eqBy (==) p result) H.failure

propHashConsedProductScaleAssociative :: Property
propHashConsedProductScaleAssociative = H.property $ do
  p <- H.forAll genHashConsedProductBV8
  let sr = HCPR.prodRepr p
  c1 <- H.forAll genBV8Coeff
  c2 <- H.forAll genBV8Coeff
  let lhs = HCPR.scale (HCPR.scale p c1) c2
  let rhs = HCPR.scale p (SR.mul sr c1 c2)
  lhs H.=== rhs

propHashConsedProductScaleDistributesOverMul :: Property
propHashConsedProductScaleDistributesOverMul = H.property $ do
  p1 <- H.forAll genHashConsedProductBV8
  p2 <- H.forAll genHashConsedProductBV8
  c <- H.forAll genBV8Coeff
  let lhs = HCPR.scale (HCPR.mul p1 p2) c
  let rhs = HCPR.mul (HCPR.scale p1 c) p2
  lhs H.=== rhs

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "SemiRing Algebraic Laws (HashConsed Product)"
  [ testProperty "Multiplication is associative" $
      H.withTests 1000 propHashConsedProductMulAssociative
  , testProperty "One is multiplicative identity" $
      H.withTests 1000 propHashConsedProductMulIdentity
  , testProperty "Scaling is associative" $
      H.withTests 1000 propHashConsedProductScaleAssociative
  , testProperty "Scaling distributes over multiplication" $
      H.withTests 1000 propHashConsedProductScaleDistributesOverMul
  ]
