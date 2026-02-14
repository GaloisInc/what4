{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.SemiRing.Bloom.Sum
  ( propBloomSumAddAssociative
  , propBloomSumAddIdentity
  , propBloomSumAddConstantAssociative
  , propBloomSumScalarDistributivity
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.NatRepr (knownNat)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.Bloom.SemiRing.Sum as BSR
import Who2.Laws.Helpers (MockExprBT(..))

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomSumBV8 :: H.Gen (BSR.SRSum (SR.SemiRingBV SR.BVArith 8) MockExprBT)
genBloomSumBV8 = do
  offset <- Gen.int (Range.linear 0 255)
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
    coeff <- Gen.int (Range.linear 0 255)
    pure (key, BV.mkBV knownNat (fromIntegral coeff))
  pure $ BSR.fromTerms (SR.SemiRingBVRepr SR.BVArithRepr knownNat) terms (BV.mkBV knownNat (fromIntegral offset))

genBV8Constant :: H.Gen (BV.BV 8)
genBV8Constant = BV.mkBV knownNat . fromIntegral <$> Gen.int (Range.linear 0 255)

-------------------------------------------------------------------------------
-- Bloom Sum Properties
-------------------------------------------------------------------------------

propBloomSumAddAssociative :: Property
propBloomSumAddAssociative = H.property $ do
  s1 <- H.forAll genBloomSumBV8
  s2 <- H.forAll genBloomSumBV8
  s3 <- H.forAll genBloomSumBV8
  let lhs = BSR.add (BSR.add s1 s2) s3
  let rhs = BSR.add s1 (BSR.add s2 s3)
  unless (BSR.size lhs < BSR.threshold && BSR.size rhs < BSR.threshold) H.discard
  lhs H.=== rhs

propBloomSumAddIdentity :: Property
propBloomSumAddIdentity = H.property $ do
  s <- H.forAll genBloomSumBV8
  let sr = BSR.sumRepr s
  let zero = BSR.constant sr (SR.zero sr)
  let result = BSR.add s zero
  unless (BSR.size result < BSR.threshold) H.discard
  unless (BSR.eqBy (==) s result) H.failure

propBloomSumAddConstantAssociative :: Property
propBloomSumAddConstantAssociative = H.property $ do
  s <- H.forAll genBloomSumBV8
  c1 <- H.forAll genBV8Constant
  c2 <- H.forAll genBV8Constant
  let lhs = BSR.addConstant (BSR.addConstant s c1) c2
  let sr = BSR.sumRepr s
  let rhs = BSR.addConstant s (SR.add sr c1 c2)
  unless (BSR.size lhs < BSR.threshold && BSR.size rhs < BSR.threshold) H.discard
  lhs H.=== rhs

propBloomSumScalarDistributivity :: Property
propBloomSumScalarDistributivity = H.property $ do
  c1 <- H.forAll genBV8Constant
  c2 <- H.forAll genBV8Constant
  x <- MockExprBT <$> H.forAll (Gen.int (Range.linear 0 100))
  let sr = SR.SemiRingBVRepr SR.BVArithRepr knownNat
  let lhs = BSR.scaledVar sr (SR.add sr c1 c2) x
  let rhs = BSR.add (BSR.scaledVar sr c1 x) (BSR.scaledVar sr c2 x)
  unless (BSR.size lhs < BSR.threshold && BSR.size rhs < BSR.threshold) H.discard
  lhs H.=== rhs
