{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.SemiRing.Bloom.Product
  ( propBloomProductMulAssociative
  , propBloomProductMulIdentity
  , propBloomProductScaleAssociative
  , propBloomProductScaleDistributesOverMul
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Data.BitVector.Sized as BV
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.Parameterized.NatRepr (knownNat)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.Bloom.SemiRing.Product as BPR
import Who2.Laws.Helpers (MockExprBT(..))

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomProductBV8 :: H.Gen (BPR.SRProd (SR.SemiRingBV SR.BVBits 8) MockExprBT)
genBloomProductBV8 = do
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
    expnt <- Gen.integral (Range.linear 1 5)
    pure (key, expnt)
  pure $ BPR.fromTerms (SR.SemiRingBVRepr SR.BVBitsRepr knownNat) terms

genBV8Coeff :: H.Gen (BV.BV 8)
genBV8Coeff = BV.mkBV knownNat . fromIntegral <$> Gen.int (Range.linear 0 255)

-------------------------------------------------------------------------------
-- Bloom Product Properties
-------------------------------------------------------------------------------

propBloomProductMulAssociative :: Property
propBloomProductMulAssociative = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  p3 <- H.forAll genBloomProductBV8
  let lhs = BPR.mul (BPR.mul p1 p2) p3
  let rhs = BPR.mul p1 (BPR.mul p2 p3)
  unless (BPR.size lhs < BPR.threshold && BPR.size rhs < BPR.threshold) H.discard
  lhs H.=== rhs

propBloomProductMulIdentity :: Property
propBloomProductMulIdentity = H.property $ do
  p <- H.forAll genBloomProductBV8
  let sr = BPR.prodRepr p
  let one = BPR.one sr
  let result = BPR.mul p one
  unless (BPR.size result < BPR.threshold) H.discard
  unless (BPR.eqBy (==) p result) H.failure

propBloomProductScaleAssociative :: Property
propBloomProductScaleAssociative = H.property $ do
  p <- H.forAll genBloomProductBV8
  let sr = BPR.prodRepr p
  c1 <- H.forAll genBV8Coeff
  c2 <- H.forAll genBV8Coeff
  let lhs = BPR.scale (BPR.scale p c1) c2
  let rhs = BPR.scale p (SR.mul sr c1 c2)
  unless (BPR.size lhs < BPR.threshold && BPR.size rhs < BPR.threshold) H.discard
  lhs H.=== rhs

propBloomProductScaleDistributesOverMul :: Property
propBloomProductScaleDistributesOverMul = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  c <- H.forAll genBV8Coeff
  let lhs = BPR.scale (BPR.mul p1 p2) c
  let rhs = BPR.mul (BPR.scale p1 c) p2
  unless (BPR.size lhs < BPR.threshold && BPR.size rhs < BPR.threshold) H.discard
  lhs H.=== rhs
