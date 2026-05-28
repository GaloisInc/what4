{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module StridedInterval (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, addNat, isPosNat, knownNat, someNat, LeqProof(..), addIsLeq, testLeq, maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.StridedInterval as S
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
import           VerifyBindings (genTest)

import qualified StridedInterval.Precision as Precision

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

  -- Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         (\d x -> S.correct_neg n d x) <$> S.genDomain n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         S.correct_add n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
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
         (\d x -> S.correct_not n d x) <$> S.genDomain n <*> genNatBV n
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
             do d <- S.genDomain w
                x <- genNatBV w
                pure (S.correct_zero_ext w d u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do d <- S.genDomain w
                x <- genNatBV w
                pure (S.correct_sign_ext w d u x)
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
         d <- S.genDomain w
         x <- genNatBV w
         pure (S.correct_select i n w d x)

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

  -- Lattice operations
  , genTest "correct_join" $
      do SW n <- genWidth
         S.correct_join n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_meet" $
      do SW n <- genWidth
         S.correct_meet n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "joinCommutative" $
      do SW n <- genWidth
         S.joinCommutative n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "joinIdempotent" $
      do SW n <- genWidth
         S.joinIdempotent n <$> S.genDomain n <*> genNatBV n
  , genTest "joinTop" $
      do SW n <- genWidth
         S.joinTop n <$> S.genDomain n <*> genNatBV n
  , genTest "joinBottom" $
      do SW n <- genWidth
         S.joinBottom n <$> S.genDomain n <*> genNatBV n
  , genTest "meetCommutative" $
      do SW n <- genWidth
         S.meetCommutative n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "meetIdempotent" $
      do SW n <- genWidth
         S.meetIdempotent n <$> S.genDomain n <*> genNatBV n
  , genTest "meetTop" $
      do SW n <- genWidth
         S.meetTop n <$> S.genDomain n <*> genNatBV n
  , genTest "meetBottom" $
      do SW n <- genWidth
         S.meetBottom n <$> S.genDomain n <*> genNatBV n
  , Precision.tests
  ]
