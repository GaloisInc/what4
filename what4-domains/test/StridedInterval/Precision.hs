-- | Precision tests for the lattice operations on the strided interval domain.
--
-- Each lifted SI op should be at least as precise as the corresponding op on
-- the @toArith@ projections of its inputs:
--
-- @
-- S.member (op a b) x ==> A.member (A.op (S.toArith a) (S.toArith b)) x
-- @
--
-- i.e. every concrete value the SI result claims is also in the Arith result on
-- the projections, so the SI result is contained in the Arith result.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module StridedInterval.Precision (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, isPosNat, someNat, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.StridedInterval as S
import           What4.Domains.Verification (Gen, Property, chooseInt, chooseInteger, getSize, property, (==>))
import           VerifyBindings (genTest)

data SomeWidth where
  SW :: (1 <= w) => NatRepr w -> SomeWidth

genWidth :: Gen SomeWidth
genWidth =
  do sz <- getSize
     x <- chooseInt (1, sz + 4)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidth"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

precise_join ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_join w a b x =
  S.member (S.join w a b) x ==>
    property (A.member (A.join (S.toArith w a) (S.toArith w b)) (toInteger x))

precise_meet ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_meet w a b x =
  S.member (S.meet w a b) x ==>
    property (A.member (A.meet (S.toArith w a) (S.toArith w b)) (toInteger x))

tests :: TT.TestTree
tests = TT.testGroup "Precision (StridedInterval at least as precise as Arith)"
  [ genTest "precise_join" $
      do SW n <- genWidth
         precise_join n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_meet" $
      do SW n <- genWidth
         precise_meet n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  ]
