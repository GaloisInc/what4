{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Laws.HashConsed.SemiRing.Sum
  ( -- eqBy properties
    propHashConsedSumEqByReflexive
  , propHashConsedSumEqBySymmetric
  , propHashConsedSumEqByTransitive
  -- ordBy properties
  , propHashConsedSumOrdByReflexive
  , propHashConsedSumOrdByAntisymmetric
  , propHashConsedSumOrdByTransitive
  , propHashConsedSumOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.NatRepr (knownNat)

import qualified What4.BaseTypes as BT
import qualified What4.SemiRing as SR

import qualified Who2.Expr.HashConsed.SemiRing.Sum as HCSR
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

genHashConsedSumBV8 :: H.Gen (HCSR.SRSum (SR.SemiRingBV SR.BVArith 8) MockExpr)
genHashConsedSumBV8 = do
  offset <- Gen.int (Range.linear 0 255)
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExpr <$> Gen.int (Range.linear 0 100)
    coeff <- Gen.int (Range.linear 0 255)
    pure (key, BV.mkBV knownNat (fromIntegral coeff))
  pure $ HCSR.fromTerms (SR.SemiRingBVRepr SR.BVArithRepr knownNat) terms (BV.mkBV knownNat (fromIntegral offset))

-------------------------------------------------------------------------------
-- eqBy Properties
-------------------------------------------------------------------------------

propHashConsedSumEqByReflexive :: Property
propHashConsedSumEqByReflexive = H.property $ do
  s <- H.forAll genHashConsedSumBV8
  H.assert $ HCSR.eqBy (==) s s

propHashConsedSumEqBySymmetric :: Property
propHashConsedSumEqBySymmetric = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  let eq1 = HCSR.eqBy (==) s1 s2
  let eq2 = HCSR.eqBy (==) s2 s1
  eq1 H.=== eq2

propHashConsedSumEqByTransitive :: Property
propHashConsedSumEqByTransitive = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  s3 <- H.forAll genHashConsedSumBV8
  let eq12 = HCSR.eqBy (==) s1 s2
  let eq23 = HCSR.eqBy (==) s2 s3
  let eq13 = HCSR.eqBy (==) s1 s3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propHashConsedSumOrdByReflexive :: Property
propHashConsedSumOrdByReflexive = H.property $ do
  s <- H.forAll genHashConsedSumBV8
  HCSR.ordBy compare s s H.=== EQ

propHashConsedSumOrdByAntisymmetric :: Property
propHashConsedSumOrdByAntisymmetric = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  let ord1 = HCSR.ordBy compare s1 s2
  let ord2 = HCSR.ordBy compare s2 s1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propHashConsedSumOrdByTransitive :: Property
propHashConsedSumOrdByTransitive = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  s3 <- H.forAll genHashConsedSumBV8
  let ord12 = HCSR.ordBy compare s1 s2
  let ord23 = HCSR.ordBy compare s2 s3
  let ord13 = HCSR.ordBy compare s1 s3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propHashConsedSumOrdByConsistentWithEqBy :: Property
propHashConsedSumOrdByConsistentWithEqBy = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  let eq = HCSR.eqBy (==) s1 s2
  let ord = HCSR.ordBy compare s1 s2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        _ -> False
  unless result H.failure
