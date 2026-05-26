{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module StridedInterval (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, isPosNat, someNat, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.StridedInterval as S
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
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

-- | Like 'genWidth' but capped at 8, for tests that enumerate the full
-- progression (which can have up to @2^w@ elements for odd strides).
genWidthSmall :: Gen SomeWidth
genWidthSmall =
  do x <- chooseInt (1, 8)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthSmall"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

tests :: TT.TestTree
tests = TT.testGroup "Strided interval domain"
  [ genTest "memberBottom" $
      do SW n <- genWidth
         S.memberBottom n <$> genNatBV n
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         S.toListMember <$> S.genDomain n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         S.memberToList <$> S.genDomain n <*> genNatBV n
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         (\d x -> S.toArithCorrect n d x) <$> S.genDomain n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         S.fromArithCorrect n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "roundtripArith" $
      do SW n <- genWidth
         (\a x -> S.roundtripArith n a x) <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         S.toBitwiseCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         S.fromBitwiseCorrect n <$> B.genDomain n <*> chooseInteger (0, maxUnsigned n)
  ]
