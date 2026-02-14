{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.SemiRing.HashConsed.Product
  ( propHashConsedProductMulAssociative
  , propHashConsedProductMulIdentity
  , propHashConsedProductScaleAssociative
  , propHashConsedProductScaleDistributesOverMul
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Data.BitVector.Sized as BV
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.Parameterized.NatRepr (knownNat)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.HashConsed.SemiRing.Product as HCPR
import Who2.Laws.Helpers (MockExprBT(..))

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genHashConsedProductBV8 :: H.Gen (HCPR.SRProd (SR.SemiRingBV SR.BVBits 8) MockExprBT)
genHashConsedProductBV8 = do
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
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
