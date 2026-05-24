{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module CLP (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, isPosNat, someNat, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.CLP as C
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

-- | Like 'genWidth' but capped at 8, for tests that enumerate the full CLP
-- (which can have up to @2^w@ elements for odd strides).
genWidthSmall :: Gen SomeWidth
genWidthSmall =
  do x <- chooseInt (1, 8)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthSmall"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

-- | An arbitrary nonnegative natural, used to seed bitvector-shaped values
-- whose width is chosen separately by 'genWidthExp'.
genNat :: Gen Natural
genNat = fromInteger <$> chooseInteger (0, 2 ^ (64 :: Int))

-- | Width exponent @k@ in @[1, sz + 4]@, used by helpers that take @2^k@ as a
-- modulus directly rather than through a 'Clp'.
genWidthExp :: Gen Int
genWidthExp =
  do sz <- getSize
     chooseInt (1, sz + 4)

-- | An odd 'Natural' in @[0, 2^64)@, suitable as input to 'invModPow2'.
genOddNat :: Gen Natural
genOddNat = (\x -> x * 2 + 1) <$> genNat

tests :: TT.TestTree
tests = TT.testGroup "Circular linear progressions (CLPs)"
  [ genTest "modNegCorrect" $
      C.modNegCorrect <$> genNat <*> genWidthExp
  , genTest "wrapOffsetCorrect" $
      do SW n <- genWidth
         C.wrapOffsetCorrect <$> C.genClp n <*> genNatBV n
  , genTest "strideGcdDividesStride" $
      do SW n <- genWidth
         C.strideGcdDividesStride <$> C.genClp n
  , genTest "strideGcdIsPow2" $
      do SW n <- genWidth
         C.strideGcdIsPow2 <$> C.genClp n
  , genTest "divByPow2Correct" $
      C.divByPow2Correct <$> genNat <*> genWidthExp
  , genTest "invModPow2Correct" $
      C.invModPow2Correct <$> genOddNat <*> genWidthExp
  , genTest "valueIndexCorrect" $
      do SW n <- genWidth
         C.valueIndexCorrect <$> C.genClp n <*> genNatBV n
  , genTest "circLeqAtZero" $
      C.circLeqAtZero <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMin" $
      C.circLeqAnchorMin <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMax" $
      C.circLeqAnchorMax <$> genNat <*> genNat <*> genWidthExp
  , genTest "startMember" $
      do SW n <- genWidth
         C.startMember <$> C.genClp n
  , genTest "endMember" $
      do SW n <- genWidth
         C.endMember <$> C.genClp n
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         C.toListMember <$> C.genClp n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         C.memberToList <$> C.genClp n <*> genNatBV n
  ]
