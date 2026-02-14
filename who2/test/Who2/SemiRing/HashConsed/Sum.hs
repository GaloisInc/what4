{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.SemiRing.HashConsed.Sum
  ( propHashConsedSumAddAssociative
  , propHashConsedSumAddCommutative
  , propHashConsedSumAddIdentity
  , propHashConsedSumAddConstantAssociative
  , propHashConsedSumScalarDistributivity
  , propHashConsedSumCancellation
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.NatRepr (knownNat)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.HashConsed.SemiRing.Sum as HCSR
import qualified Who2.Expr.HashConsed.Map as EM
import Who2.Laws.Helpers (MockExprBT(..))

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genHashConsedSumBV8 :: H.Gen (HCSR.SRSum (SR.SemiRingBV SR.BVArith 8) MockExprBT)
genHashConsedSumBV8 = do
  offset <- Gen.int (Range.linear 0 255)
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
    coeff <- Gen.int (Range.linear 0 255)
    pure (key, BV.mkBV knownNat (fromIntegral coeff))
  pure $ HCSR.fromTerms (SR.SemiRingBVRepr SR.BVArithRepr knownNat) terms (BV.mkBV knownNat (fromIntegral offset))

genBV8Constant :: H.Gen (BV.BV 8)
genBV8Constant = BV.mkBV knownNat . fromIntegral <$> Gen.int (Range.linear 0 255)

-------------------------------------------------------------------------------
-- HashConsed Sum Properties
-------------------------------------------------------------------------------

propHashConsedSumAddAssociative :: Property
propHashConsedSumAddAssociative = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  s3 <- H.forAll genHashConsedSumBV8
  let lhs = HCSR.add (HCSR.add s1 s2) s3
  let rhs = HCSR.add s1 (HCSR.add s2 s3)
  lhs H.=== rhs

propHashConsedSumAddCommutative :: Property
propHashConsedSumAddCommutative = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  let lhs = HCSR.add s1 s2
  let rhs = HCSR.add s2 s1
  lhs H.=== rhs

propHashConsedSumAddIdentity :: Property
propHashConsedSumAddIdentity = H.property $ do
  s <- H.forAll genHashConsedSumBV8
  let sr = HCSR.sumRepr s
  let zero = HCSR.constant sr (SR.zero sr)
  let result = HCSR.add s zero
  unless (HCSR.eqBy (==) s result) H.failure

propHashConsedSumAddConstantAssociative :: Property
propHashConsedSumAddConstantAssociative = H.property $ do
  s <- H.forAll genHashConsedSumBV8
  c1 <- H.forAll genBV8Constant
  c2 <- H.forAll genBV8Constant
  let lhs = HCSR.addConstant (HCSR.addConstant s c1) c2
  let sr = HCSR.sumRepr s
  let rhs = HCSR.addConstant s (SR.add sr c1 c2)
  lhs H.=== rhs

propHashConsedSumScalarDistributivity :: Property
propHashConsedSumScalarDistributivity = H.property $ do
  c1 <- H.forAll genBV8Constant
  c2 <- H.forAll genBV8Constant
  x <- MockExprBT <$> H.forAll (Gen.int (Range.linear 0 100))
  let sr = SR.SemiRingBVRepr SR.BVArithRepr knownNat
  let lhs = HCSR.scaledVar sr (SR.add sr c1 c2) x
  let rhs = HCSR.add (HCSR.scaledVar sr c1 x) (HCSR.scaledVar sr c2 x)
  lhs H.=== rhs

propHashConsedSumCancellation :: Property
propHashConsedSumCancellation = H.property $ do
  c <- H.forAll genBV8Constant
  x <- MockExprBT <$> H.forAll (Gen.int (Range.linear 0 100))
  let sr = SR.SemiRingBVRepr SR.BVArithRepr knownNat
  let negC = BV.negate knownNat c  -- Compute -c for BV arithmetic
  let result = HCSR.add (HCSR.scaledVar sr c x) (HCSR.scaledVar sr negC x)
  -- After cancellation, the map should be empty (no zero-coefficient terms)
  H.assert $ EM.size (HCSR.sumMap result) == 0
