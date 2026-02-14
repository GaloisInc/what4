{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Laws.Bloom.SemiRing.Product
  ( -- eqBy properties
    propBloomProductEqByReflexive
  , propBloomProductEqBySymmetric
  , propBloomProductEqByTransitive
  -- ordBy properties
  , propBloomProductOrdByReflexive
  , propBloomProductOrdByAntisymmetric
  , propBloomProductOrdByTransitive
  , propBloomProductOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.BitVector.Sized()

import Data.Parameterized.NatRepr (knownNat)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.Bloom.SemiRing.Product as SRP
import Who2.Laws.Helpers (MockExprBT(..), checkOrdTransitivity, checkOrdAntisymmetry)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomProductBV8 :: H.Gen (SRP.SRProd (SR.SemiRingBV SR.BVBits 8) MockExprBT)
genBloomProductBV8 = do
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
    expnt <- Gen.integral (Range.linear 1 5)
    pure (key, expnt)
  pure $ SRP.fromTerms (SR.SemiRingBVRepr SR.BVBitsRepr knownNat) terms

-------------------------------------------------------------------------------
-- eqBy Properties
-------------------------------------------------------------------------------

propBloomProductEqByReflexive :: Property
propBloomProductEqByReflexive = H.property $ do
  p <- H.forAll genBloomProductBV8
  H.assert $ SRP.eqBy (==) p p

propBloomProductEqBySymmetric :: Property
propBloomProductEqBySymmetric = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  let eq1 = SRP.eqBy (==) p1 p2
  let eq2 = SRP.eqBy (==) p2 p1
  eq1 H.=== eq2

propBloomProductEqByTransitive :: Property
propBloomProductEqByTransitive = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  p3 <- H.forAll genBloomProductBV8
  let eq12 = SRP.eqBy (==) p1 p2
  let eq23 = SRP.eqBy (==) p2 p3
  let eq13 = SRP.eqBy (==) p1 p3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propBloomProductOrdByReflexive :: Property
propBloomProductOrdByReflexive = H.property $ do
  p <- H.forAll genBloomProductBV8
  SRP.ordBy compare p p H.=== EQ

propBloomProductOrdByAntisymmetric :: Property
propBloomProductOrdByAntisymmetric = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  let ord1 = SRP.ordBy compare p1 p2
  let ord2 = SRP.ordBy compare p2 p1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propBloomProductOrdByTransitive :: Property
propBloomProductOrdByTransitive = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  p3 <- H.forAll genBloomProductBV8
  let ord12 = SRP.ordBy compare p1 p2
  let ord23 = SRP.ordBy compare p2 p3
  let ord13 = SRP.ordBy compare p1 p3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propBloomProductOrdByConsistentWithEqBy :: Property
propBloomProductOrdByConsistentWithEqBy = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  let eq = SRP.eqBy (==) p1 p2
  let ord = SRP.ordBy compare p1 p2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        (True, LT) -> False
        (True, GT) -> False
        (False, EQ) -> False
  unless result H.failure
