{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Strides (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.Strides as S
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
import           VerifyBindings (genTest)

import qualified Strides.Precision as Precision

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

-- | Like 'genWidth' but capped at 8, for tests that enumerate the full progression
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
-- modulus directly rather than through a progression.
genWidthExp :: Gen Int
genWidthExp =
  do sz <- getSize
     chooseInt (1, sz + 4)

-- | An odd 'Natural' in @[0, 2^64)@, suitable as input to 'invModPow2'.
genOddNat :: Gen Natural
genOddNat = (\x -> x * 2 + 1) <$> genNat

tests :: TT.TestTree
tests = TT.testGroup "Strides"
  [ genTest "modNegCorrect" $
      S.modNegCorrect <$> genNat <*> genWidthExp
  , genTest "modSubCorrect" $
      S.modSubCorrect <$> genNat <*> genNat <*> genWidthExp
  , genTest "firstCosetMemberCorrect" $
      S.firstCosetMemberCorrect <$> genNat <*> genNat <*> genWidthExp <*> genWidthExp
  , genTest "wrapOffsetCorrect" $
      do SW n <- genWidth
         S.wrapOffsetCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "strideGcdDividesStride" $
      do SW n <- genWidth
         S.strideGcdDividesStride <$> S.genDomain n
  , genTest "strideGcdIsPow2" $
      do SW n <- genWidth
         S.strideGcdIsPow2 <$> S.genDomain n
  , genTest "orbitLenViaToList" $
      do SW n <- genWidthSmall
         S.orbitLenViaToList <$> S.genDomain n
  , genTest "divByPow2Correct" $
      S.divByPow2Correct <$> genNat <*> genWidthExp
  , genTest "invModPow2Correct" $
      S.invModPow2Correct <$> genOddNat <*> genWidthExp
  , genTest "floorSumCorrect" $
      S.floorSumCorrect <$> genNat <*> genNat <*> genNat <*> genNat
  , genTest "valueIndexCorrect" $
      do SW n <- genWidth
         S.valueIndexCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "valueIndexMaybeCorrect" $
      do SW n <- genWidth
         S.valueIndexMaybeCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "valueAtCorrect" $
      do SW n <- genWidth
         S.valueAtCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "circLeqAtZero" $
      S.circLeqAtZero <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMin" $
      S.circLeqAnchorMin <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMax" $
      S.circLeqAnchorMax <$> genNat <*> genNat <*> genWidthExp
  , genTest "isSelfWrappingViaToList" $
      do SW n <- genWidthSmall
         S.isSelfWrappingViaToList <$> S.genDomain n
  , genTest "startMember" $
      do SW n <- genWidth
         S.startMember <$> S.genDomain n
  , genTest "endMember" $
      do SW n <- genWidth
         S.endMember <$> S.genDomain n
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         S.toListMember <$> S.genDomain n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         S.memberToList <$> S.genDomain n <*> genNatBV n
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         S.toListNoDuplicates <$> S.genDomain n
  , genTest "leqCorrect" $
      do SW n <- genWidthSmall
         S.leqCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         S.leqReflexive <$> S.genDomain n
  , genTest "leqTransitive" $
      do SW n <- genWidth
         S.leqTransitive <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "leqRefinesLeqExact" $
      do SW n <- genWidthSmall
         S.leqRefinesLeqExact <$> S.genDomain n <*> S.genDomain n
  , genTest "leqPreciseCorrect" $
      do SW n <- genWidthSmall
         S.leqPreciseCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "leqPreciseReflexive" $
      do SW n <- genWidth
         S.leqPreciseReflexive <$> S.genDomain n
  , genTest "leqPreciseRefinesLeqExact" $
      do SW n <- genWidthSmall
         S.leqPreciseRefinesLeqExact <$> S.genDomain n <*> S.genDomain n
  , genTest "leqExactCorrect" $
      do SW n <- genWidthSmall
         S.leqExactCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "leqExactComplete" $
      do SW n <- genWidthSmall
         S.leqExactComplete <$> S.genDomain n <*> S.genDomain n
  , genTest "leqExactReflexive" $
      do SW n <- genWidth
         S.leqExactReflexive <$> S.genDomain n
  , genTest "leqExactTransitive" $
      do SW n <- genWidth
         S.leqExactTransitive <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "sizeViaToList" $
      do SW n <- genWidthSmall
         S.sizeViaToList <$> S.genDomain n
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         S.toArithCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "startEndArcCorrect" $
      do SW n <- genWidth
         S.startEndArcCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "cosetArcCorrect" $
      do SW n <- genWidth
         S.cosetArcCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         S.fromArithCorrect n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "roundtripArith" $
      do SW n <- genWidth
         S.roundtripArith n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         S.toBitwiseCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         S.fromBitwiseCorrect n <$> B.genDomain n <*> chooseInteger (0, maxUnsigned n)

  -- Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         (\c x -> S.correct_neg n c x) <$> S.genDomain n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         S.correct_add n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sub" $
      do SW n <- genWidth
         S.correct_sub n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_scale" $
      do SW n <- genWidth
         S.correct_scale n <$> chooseInteger (0, maxUnsigned n)
                           <*> S.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         S.correct_mul n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         S.correct_udiv n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         S.correct_urem n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         S.correct_sdiv n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         S.correct_srem n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         S.correct_udivSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         S.correct_uremSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         S.correct_sdivSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         S.correct_sremSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n

  -- Bitwise
  , genTest "correct_not" $
      do SW n <- genWidth
         (\c x -> S.correct_not n c x) <$> S.genDomain n <*> genNatBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         S.correct_and n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         S.correct_or n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         S.correct_xor n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n

  -- Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV w
                pure (S.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV w
                pure (S.correct_sign_ext w c u x)
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- S.genDomain m
         x <- genNatBV m
         b <- S.genDomain n
         y <- genNatBV n
         pure (S.correct_concat m a x n b y)
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- S.genDomain w
         x <- genNatBV w
         pure (S.correct_select i n w c x)

  -- Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         S.correct_shl n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         S.correct_lshr n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         S.correct_ashr n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_rol" $
      do SW n <- genWidth
         S.correct_rol n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_ror" $
      do SW n <- genWidth
         S.correct_ror n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , Precision.tests
  ]
