{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Laws.HashConsed.SemiRing.Product
  ( -- eqBy properties
    propHashConsedProductEqByReflexive
  , propHashConsedProductEqBySymmetric
  , propHashConsedProductEqByTransitive
  -- ordBy properties
  , propHashConsedProductOrdByReflexive
  , propHashConsedProductOrdByAntisymmetric
  , propHashConsedProductOrdByTransitive
  , propHashConsedProductOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.Parameterized.NatRepr (knownNat)

import qualified What4.BaseTypes as BT
import qualified What4.SemiRing as SR

import qualified Who2.Expr.HashConsed.SemiRing.Product as HCPR
import Who2.Expr (HasId(..))
import Who2.Laws.Helpers (checkOrdTransitivity, checkOrdAntisymmetry)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

-- Mock expression type for testing (kind: BaseType -> *)
newtype MockExpr (tp :: BT.BaseType) = MockExpr Int
  deriving (Eq, Ord, Show)

instance HasId (MockExpr tp) where
  getId (MockExpr i) = i

genHashConsedProductBV8 :: H.Gen (HCPR.SRProd (SR.SemiRingBV SR.BVBits 8) MockExpr)
genHashConsedProductBV8 = do
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExpr <$> Gen.int (Range.linear 0 100)
    expnt <- Gen.integral (Range.linear 1 5)
    pure (key, expnt)
  pure $ HCPR.fromTerms (SR.SemiRingBVRepr SR.BVBitsRepr knownNat) terms

-------------------------------------------------------------------------------
-- eqBy Properties
-------------------------------------------------------------------------------

propHashConsedProductEqByReflexive :: Property
propHashConsedProductEqByReflexive = H.property $ do
  p <- H.forAll genHashConsedProductBV8
  H.assert $ HCPR.eqBy (==) p p

propHashConsedProductEqBySymmetric :: Property
propHashConsedProductEqBySymmetric = H.property $ do
  p1 <- H.forAll genHashConsedProductBV8
  p2 <- H.forAll genHashConsedProductBV8
  let eq1 = HCPR.eqBy (==) p1 p2
  let eq2 = HCPR.eqBy (==) p2 p1
  eq1 H.=== eq2

propHashConsedProductEqByTransitive :: Property
propHashConsedProductEqByTransitive = H.property $ do
  p1 <- H.forAll genHashConsedProductBV8
  p2 <- H.forAll genHashConsedProductBV8
  p3 <- H.forAll genHashConsedProductBV8
  let eq12 = HCPR.eqBy (==) p1 p2
  let eq23 = HCPR.eqBy (==) p2 p3
  let eq13 = HCPR.eqBy (==) p1 p3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propHashConsedProductOrdByReflexive :: Property
propHashConsedProductOrdByReflexive = H.property $ do
  p <- H.forAll genHashConsedProductBV8
  HCPR.ordBy compare p p H.=== EQ

propHashConsedProductOrdByAntisymmetric :: Property
propHashConsedProductOrdByAntisymmetric = H.property $ do
  p1 <- H.forAll genHashConsedProductBV8
  p2 <- H.forAll genHashConsedProductBV8
  let ord1 = HCPR.ordBy compare p1 p2
  let ord2 = HCPR.ordBy compare p2 p1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propHashConsedProductOrdByTransitive :: Property
propHashConsedProductOrdByTransitive = H.property $ do
  p1 <- H.forAll genHashConsedProductBV8
  p2 <- H.forAll genHashConsedProductBV8
  p3 <- H.forAll genHashConsedProductBV8
  let ord12 = HCPR.ordBy compare p1 p2
  let ord23 = HCPR.ordBy compare p2 p3
  let ord13 = HCPR.ordBy compare p1 p3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propHashConsedProductOrdByConsistentWithEqBy :: Property
propHashConsedProductOrdByConsistentWithEqBy = H.property $ do
  p1 <- H.forAll genHashConsedProductBV8
  p2 <- H.forAll genHashConsedProductBV8
  let eq = HCPR.eqBy (==) p1 p2
  let ord = HCPR.ordBy compare p1 p2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        _ -> False
  unless result H.failure
