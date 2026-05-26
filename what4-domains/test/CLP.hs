{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module CLP (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
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
  , genTest "isMultiWrapViaToList" $
      do SW n <- genWidthSmall
         C.isMultiWrapViaToList <$> C.genClp n
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
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         C.toListNoDuplicates <$> C.genClp n
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         C.toArithCorrect n <$> C.genClp n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         C.fromArithCorrect n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "roundtripArith" $
      do SW n <- genWidth
         C.roundtripArith n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         C.toBitwiseCorrect n <$> C.genClp n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         C.fromBitwiseCorrect n <$> B.genDomain n <*> chooseInteger (0, maxUnsigned n)

  -- Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         (\c x -> C.correct_neg n c x) <$> C.genClp n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         C.correct_add n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_scale" $
      do SW n <- genWidth
         C.correct_scale n <$> chooseInteger (0, maxUnsigned n)
                           <*> C.genClp n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         C.correct_mul n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         C.correct_udiv n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         C.correct_urem n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         C.correct_sdiv n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         C.correct_srem n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         C.correct_udivSmtlib n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         C.correct_uremSmtlib n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         C.correct_sdivSmtlib n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         C.correct_sremSmtlib n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n

  -- Bitwise
  , genTest "correct_not" $
      do SW n <- genWidth
         (\c x -> C.correct_not n c x) <$> C.genClp n <*> genNatBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         C.correct_and n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         C.correct_or n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         C.correct_xor n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n

  -- Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- C.genClp w
                x <- genNatBV w
                pure (C.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- C.genClp w
                x <- genNatBV w
                pure (C.correct_sign_ext w c u x)
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- C.genClp m
         x <- genNatBV m
         b <- C.genClp n
         y <- genNatBV n
         pure (C.correct_concat m a x n b y)
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- C.genClp w
         x <- genNatBV w
         pure (C.correct_select i n w c x)

  -- Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         C.correct_shl n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         C.correct_lshr n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         C.correct_ashr n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_rol" $
      do SW n <- genWidth
         C.correct_rol n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  , genTest "correct_ror" $
      do SW n <- genWidth
         C.correct_ror n <$> C.genClp n <*> genNatBV n <*> C.genClp n <*> genNatBV n
  ]
