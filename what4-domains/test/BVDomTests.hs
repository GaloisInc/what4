{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-
Module      : BVDomTest
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : rdockins@galois.com

This module performs randomized testing of the bitvector abstract domain
computations, which are among relatively complex.

The intended meaning of the abstract domain computations are
specified using Cryptol in "doc/bvdomain.cry" and realated files.
In those files soundness properites are proved for the implementations.
These tests are intended to supplement those proofs for the actual
implementations, which are transliterated from the Cryptol.
-}

import qualified Data.Bits as Bits
import           Numeric.Natural
import           Test.Tasty
import           Test.Tasty.HUnit
import           What4.Domains.Verification
import           VerifyBindings
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import qualified What4.Domains.BV as O
import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.XOR as X
import           What4.Domains.Internal (assertionsEnabled)
import qualified What4.Domains.Arithmetic.Internal as ArithOpt



main :: IO ()
main = defaultMain $
  setTestOptions $

    testGroup "Bitvector Domain"
    [ -- See Note [Asserts] in what4-domains
      testCase "assertions enabled" $ do
        assertsEnabled <- assertionsEnabled
        assertBool "assertions should be enabled" assertsEnabled
    , arithmeticOptimiztionTests
    , arithDomainTests
    , bitwiseDomainTests
    , xorDomainTests
    , overallDomainTests
    , transferTests
    ]

data SomeWidth where
  SW :: (1 <= w) => NatRepr w -> SomeWidth

genWidth :: Gen SomeWidth
genWidth =
  do sz <- getSize
     x <- chooseInt (1, sz + 4)
     case someNat x of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidth"

-- | Like 'genWidth' but capped at 6, for tests whose oracle is
-- exponential in the width.
genWidthSmall :: Gen SomeWidth
genWidthSmall =
  do x <- chooseInt (1, 6)
     case someNat x of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthSmall"

-- | A small power-of-two width, capped at 8, for equivalence tests
-- whose oracle iterates over @[0, 2^w - 1]@. Power-of-two widths matter
-- for rotate equivalence: at those widths @s mod w == s & (w-1)@,
-- enabling an LLVM-style tristate decomposition.
genWidthPow2Small :: Gen SomeWidth
genWidthPow2Small =
  do i <- chooseInt (0, 3)
     case someNat (([1, 2, 4, 8] :: [Natural]) !! i) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthPow2Small"

genBV :: NatRepr w -> Gen Integer
genBV w = chooseInteger (minUnsigned w, maxUnsigned w)


arithDomainTests :: TestTree
arithDomainTests = testGroup "Arith Domain"
  [ genTest "correct_any" $
      do SW n <- genWidth
         A.correct_any n <$> genBV n
  , genTest "correct_ubounds" $
      do SW n <- genWidth
         A.correct_ubounds n <$> A.genPair n
  , genTest "correct_sbounds" $
      do SW n <- genWidth
         A.correct_sbounds n <$> A.genPair n
  , genTest "correct_singleton" $
      do SW n <- genWidth
         A.correct_singleton n <$> genBV n <*> genBV n
  , genTest "correct_overlap" $
      do SW n <- genWidth
         A.correct_overlap <$> A.genDomain n <*> A.genDomain n <*> genBV n
  , genTest "correct_overlap_inv" $
      do SW n <- genWidth
         A.correct_overlap_inv <$> A.genDomain n <*> A.genDomain n
  , genTest "correct_asSingleton" $
      do SW n <- genWidth
         A.correct_asSingleton n <$> A.genDomain n
  , genTest "correct_mulRange" $
      do SW n <- genWidth
         a <- (,) <$> genBV n <*> genBV n
         b <- (,) <$> genBV n <*> genBV n
         x <- genBV n
         y <- genBV n
         pure $ A.correct_mulRange a b x y
  , genTest "correct_union" $
      do SW n <- genWidth
         A.correct_union n <$> A.genDomain n <*> A.genDomain n <*> genBV n
  , genTest "correct_join" $
      do SW n <- genWidth
         A.correct_join n <$> A.genDomain n <*> A.genDomain n <*> genBV n
  , genTest "correct_meet" $
      do SW n <- genWidth
         A.correct_meet <$> A.genDomain n <*> A.genDomain n <*> genBV n
  , genTest "correct_leq" $
      do SW n <- genWidth
         A.correct_leq <$> A.genDomain n <*> A.genDomain n <*> genBV n
  , genTest "join_commutative" $
      do SW n <- genWidth
         A.join_commutative <$> A.genDomain n <*> A.genDomain n <*> genBV n
  , genTest "join_idempotent" $
      do SW n <- genWidth
         A.join_idempotent <$> A.genDomain n <*> genBV n
  , genTest "meet_commutative" $
      do SW n <- genWidth
         A.meet_commutative <$> A.genDomain n <*> A.genDomain n <*> genBV n
  , genTest "meet_idempotent" $
      do SW n <- genWidth
         A.meet_idempotent <$> A.genDomain n <*> genBV n
  , genTest "join_top" $
      do SW n <- genWidth
         A.join_top n <$> A.genDomain n <*> genBV n
  , genTest "join_bottom" $
      do SW n <- genWidth
         A.join_bottom n <$> A.genDomain n <*> genBV n
  , genTest "meet_top" $
      do SW n <- genWidth
         A.meet_top n <$> A.genDomain n <*> genBV n
  , genTest "meet_bottom" $
      do SW n <- genWidth
         A.meet_bottom n <$> A.genDomain n <*> genBV n
  , genTest "leq_reflexive" $
      do SW n <- genWidth
         A.leq_reflexive <$> A.genDomain n
  , genTest "join_upper_bound" $
      do SW n <- genWidth
         A.join_upper_bound <$> A.genDomain n <*> A.genDomain n
  , genTest "join_proper" $
      do SW n <- genWidth
         A.join_proper n <$> A.genDomain n <*> A.genDomain n
  , genTest "meet_proper" $
      do SW n <- genWidth
         A.meet_proper n <$> A.genDomain n <*> A.genDomain n
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- A.genDomain w
                x <- A.genElement a
                pure $ A.correct_zero_ext w a u x
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- A.genDomain w
                x <- A.genElement a
                pure $ A.correct_sign_ext w a u x
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         A.correct_concat m <$> A.genPair m <*> pure n <*> A.genPair n
  , genTest "correct_shrink" $
      do SW i <- genWidth
         SW n <- genWidth
         A.correct_shrink i n <$> A.genPair (addNat i n)
  , genTest "correct_trunc" $
      do SW n <- genWidth
         SW m <- genWidth
         let w = addNat n m
         LeqProof <- pure $ addIsLeq n m
         A.correct_trunc n <$> A.genPair w
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure $ addIsLeq i_n z
         A.correct_select i n <$> A.genPair w
  , genTest "correct_add" $
      do SW n <- genWidth
         A.correct_add n <$> A.genPair n <*> A.genPair n
  , genTest "correct_sub" $
      do SW n <- genWidth
         A.correct_sub n <$> A.genPair n <*> A.genPair n
  , genTest "correct_neg" $
      do SW n <- genWidth
         A.correct_neg n <$> A.genPair n
  , genTest "correct_not" $
      do SW n <- genWidth
         A.correct_not n <$> A.genPair n
  , genTest "correct_and" $
      do SW n <- genWidth
         A.correct_and n <$> A.genPair n <*> A.genPair n
  , genTest "correct_or" $
      do SW n <- genWidth
         A.correct_or n <$> A.genPair n <*> A.genPair n
  , genTest "correct_xor" $
      do SW n <- genWidth
         A.correct_xor n <$> A.genPair n <*> A.genPair n
  , genTest "correct_mul" $
      do SW n <- genWidth
         A.correct_mul n <$> A.genPair n <*> A.genPair n
  , genTest "correct_scale" $
      do SW n <- genWidth
         A.correct_scale n <$> genBV n <*> A.genPair n
  , genTest "correct_scale_eq" $
      do SW n <- genWidth
         A.correct_scale_eq n <$> genBV n <*> A.genDomain n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         A.correct_udiv n <$> A.genPair n <*> A.genPair n
  , genTest "correct_urem" $
      do SW n <- genWidth
         A.correct_urem n <$> A.genPair n <*> A.genPair n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         A.correct_sdiv n <$> A.genPair n <*> A.genPair n
  , genTest "correct_sdivRange" $
      do SW n <- genWidth
         a <- (,) <$> genBV n <*> genBV n
         b <- (,) <$> genBV n <*> genBV n
         x <- genBV n
         y <- genBV n
         pure $ A.correct_sdivRange a b x y
  , genTest "correct_srem" $
      do SW n <- genWidth
         A.correct_srem n <$> A.genPair n <*> A.genPair n
  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         A.correct_udivSmtlib n <$> A.genPair n <*> A.genPair n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         A.correct_uremSmtlib n <$> A.genPair n <*> A.genPair n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         A.correct_sdivSmtlib n <$> A.genPair n <*> A.genPair n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         A.correct_sremSmtlib n <$> A.genPair n <*> A.genPair n
  , genTest "correct_shl" $
      do SW n <- genWidth
         A.correct_shl n <$> A.genPair n <*> A.genPair n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         A.correct_lshr n <$> A.genPair n <*> A.genPair n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         A.correct_ashr n <$> A.genPair n <*> A.genPair n
  , genTest "correct_rol" $
      do SW n <- genWidth
         A.correct_rol n <$> A.genPair n <*> A.genPair n
  , genTest "correct_ror" $
      do SW n <- genWidth
         A.correct_ror n <$> A.genPair n <*> A.genPair n
  , genTest "correct_eq" $
      do SW n <- genWidth
         A.correct_eq n <$> A.genPair n <*> A.genPair n
  , genTest "correct_ult" $
      do SW n <- genWidth
         A.correct_ult n <$> A.genPair n <*> A.genPair n
  , genTest "correct_slt" $
      do SW n <- genWidth
         A.correct_slt n <$> A.genPair n <*> A.genPair n
  , genTest "correct_isUltSumCommonEquiv" $
      do SW n <- genWidth
         A.correct_isUltSumCommonEquiv n <$> A.genPair n <*> A.genPair n <*> A.genPair n
  , genTest "correct_unknowns" $
      do SW n <- genWidth
         a <- A.genDomain n
         x <- A.genElement a
         y <- A.genElement a
         pure $ A.correct_unknowns a x y
  , genTest "correct_bitbounds" $
      do SW n <- genWidth
         A.correct_bitbounds n <$> A.genPair n
  , genTest "correct_toBitwise" $
      do SW n <- genWidth
         A.correct_toBitwise n <$> A.genPair n
  , genTest "correct_fromBitwise" $
      do SW n <- genWidth
         A.correct_fromBitwise n <$> B.genPair n
  ]

xorDomainTests :: TestTree
xorDomainTests =
  testGroup "XOR Domain"
  [ genTest "correct_singleton" $
      do SW n <- genWidth
         X.correct_singleton n <$> genBV n <*> genBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         X.correct_xor n <$> X.genPair n <*> X.genPair n
  , genTest "correct_and" $
      do SW n <- genWidth
         X.correct_and n <$> X.genPair n <*> X.genPair n
  , genTest "correct_and_scalar" $
      do SW n <- genWidth
         X.correct_and_scalar n <$> genBV n <*> X.genPair n
  , genTest "correct_bitbounds" $
      do SW n <- genWidth
         X.correct_bitbounds <$> X.genDomain n <*> genBV n
  ]

bitwiseDomainTests :: TestTree
bitwiseDomainTests =
  testGroup "Bitwise Domain"
  [ genTest "correct_any" $
      do SW n <- genWidth
         B.correct_any n <$> genBV n
  , genTest "correct_singleton" $
      do SW n <- genWidth
         B.correct_singleton n <$> genBV n <*> genBV n
  , genTest "correct_overlap" $
      do SW n <- genWidth
         B.correct_overlap <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "correct_overlap_inv" $
      do SW n <- genWidth
         B.correct_overlap_inv <$> B.genDomain n <*> B.genDomain n
  , genTest "correct_asSingleton" $
      do SW n <- genWidth
         B.correct_asSingleton n <$> B.genDomain n
  , genTest "correct_union1" $
      do SW n <- genWidth
         (a,x) <- B.genPair n
         b <- B.genDomain n
         pure $ B.correct_union n a b x
  , genTest "correct_union2" $
      do SW n <- genWidth
         a <- B.genDomain n
         (b,x) <- B.genPair n
         pure $ B.correct_union n a b x
  , genTest "correct_intersection" $
      do SW n <- genWidth
         B.correct_intersection <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "correct_join" $
      do SW n <- genWidth
         B.correct_join n <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "correct_meet" $
      do SW n <- genWidth
         B.correct_meet <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "precise_meet" $
      do SW n <- genWidth
         B.precise_meet <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "correct_leq" $
      do SW n <- genWidth
         B.correct_leq <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "join_commutative" $
      do SW n <- genWidth
         B.join_commutative <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "join_idempotent" $
      do SW n <- genWidth
         B.join_idempotent <$> B.genDomain n <*> genBV n
  , genTest "meet_commutative" $
      do SW n <- genWidth
         B.meet_commutative <$> B.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "meet_idempotent" $
      do SW n <- genWidth
         B.meet_idempotent <$> B.genDomain n <*> genBV n
  , genTest "join_top" $
      do SW n <- genWidth
         B.join_top n <$> B.genDomain n <*> genBV n
  , genTest "join_bottom" $
      do SW n <- genWidth
         B.join_bottom n <$> B.genDomain n <*> genBV n
  , genTest "meet_top" $
      do SW n <- genWidth
         B.meet_top n <$> B.genDomain n <*> genBV n
  , genTest "meet_bottom" $
      do SW n <- genWidth
         B.meet_bottom n <$> B.genDomain n <*> genBV n
  , genTest "leq_reflexive" $
      do SW n <- genWidth
         B.leq_reflexive <$> B.genDomain n
  , genTest "join_upper_bound" $
      do SW n <- genWidth
         B.join_upper_bound <$> B.genDomain n <*> B.genDomain n
  , genTest "join_proper" $
      do SW n <- genWidth
         B.join_proper n <$> B.genDomain n <*> B.genDomain n
  , genTest "meet_proper" $
      do SW n <- genWidth
         B.meet_proper n <$> B.genDomain n <*> B.genDomain n
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- B.genDomain w
                x <- B.genElement a
                pure $ B.correct_zero_ext w a u x
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- B.genDomain w
                x <- B.genElement a
                pure $ B.correct_sign_ext w a u x
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         B.correct_concat m <$> B.genPair m <*> pure n <*> B.genPair n
  , genTest "correct_shrink" $
      do SW i <- genWidth
         SW n <- genWidth
         B.correct_shrink i n <$> B.genPair (addNat i n)
  , genTest "correct_trunc" $
      do SW n <- genWidth
         SW m <- genWidth
         let w = addNat n m
         LeqProof <- pure $ addIsLeq n m
         B.correct_trunc n <$> B.genPair w
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure $ addIsLeq i_n z
         B.correct_select i n <$> B.genPair w
  , genTest "correct_shl" $
      do SW n <- genWidth
         B.correct_shl n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_lshr" $
      do SW n <- genWidth
         B.correct_lshr n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_ashr" $
      do SW n <- genWidth
         B.correct_ashr n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_rol" $
      do SW n <- genWidth
         B.correct_rol n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_ror" $
      do SW n <- genWidth
         B.correct_ror n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_shlAbstract" $
      do SW n <- genWidth
         B.correct_shlAbstract n <$> B.genPair n <*> B.genPair n
  , genTest "correct_lshrAbstract" $
      do SW n <- genWidth
         B.correct_lshrAbstract n <$> B.genPair n <*> B.genPair n
  , genTest "correct_ashrAbstract" $
      do SW n <- genWidth
         B.correct_ashrAbstract n <$> B.genPair n <*> B.genPair n
  , genTest "correct_rolAbstract" $
      do SW n <- genWidth
         B.correct_rolAbstract n <$> B.genPair n <*> B.genPair n
  , genTest "correct_rorAbstract" $
      do SW n <- genWidth
         B.correct_rorAbstract n <$> B.genPair n <*> B.genPair n
  , genTest "correct_equiv_shlAbstract" $
      do SW n <- genWidthSmall
         B.correct_equiv_shlAbstract n <$> B.genDomain n <*> B.genDomain n
  , genTest "correct_equiv_lshrAbstract" $
      do SW n <- genWidthSmall
         B.correct_equiv_lshrAbstract n <$> B.genDomain n <*> B.genDomain n
  , genTest "correct_equiv_ashrAbstract" $
      do SW n <- genWidthSmall
         B.correct_equiv_ashrAbstract n <$> B.genDomain n <*> B.genDomain n
  -- Rotate equivalence holds only at power-of-two widths (where
  -- @s mod w == s & (w-1)@ enables an LLVM-style tristate decomposition).
  -- At non-power-of-two widths the optimized version is sound but may
  -- be less precise than the spec.
  , genTest "correct_equiv_rolAbstract" $
      do SW n <- genWidthPow2Small
         B.correct_equiv_rolAbstract n <$> B.genDomain n <*> B.genDomain n
  , genTest "correct_equiv_rorAbstract" $
      do SW n <- genWidthPow2Small
         B.correct_equiv_rorAbstract n <$> B.genDomain n <*> B.genDomain n
  , genTest "correct_eq" $
      do SW n <- genWidth
         B.correct_eq n <$> B.genPair n <*> B.genPair n
  , genTest "correct_not" $
      do SW n <- genWidth
         B.correct_not n <$> B.genPair n
  , genTest "correct_and" $
      do SW n <- genWidth
         B.correct_and n <$> B.genPair n <*> B.genPair n
  , genTest "correct_or" $
      do SW n <- genWidth
         B.correct_or n <$> B.genPair n <*> B.genPair n
  , genTest "correct_xor" $
      do SW n <- genWidth
         B.correct_xor n <$> B.genPair n <*> B.genPair n
  , genTest "correct_testBit" $
      do SW n <- genWidth
         i <- fromInteger <$> chooseInteger (0, intValue n - 1)
         B.correct_testBit n <$> B.genPair n <*> pure i
  , genTest "correct_ubounds" $
      do SW n <- genWidth
         B.correct_ubounds n <$> B.genPair n
  , genTest "correct_sbounds" $
      do SW n <- genWidth
         B.correct_sbounds n <$> B.genPair n
  , genTest "correct_ult" $
      do SW n <- genWidth
         B.correct_ult n <$> B.genPair n <*> B.genPair n
  , genTest "correct_slt" $
      do SW n <- genWidth
         B.correct_slt n <$> B.genPair n <*> B.genPair n
  , genTest "correct_add" $
      do SW n <- genWidth
         B.correct_add n <$> B.genPair n <*> B.genPair n
  , genTest "correct_sub" $
      do SW n <- genWidth
         B.correct_sub n <$> B.genPair n <*> B.genPair n
  , genTest "correct_neg" $
      do SW n <- genWidth
         B.correct_neg n <$> B.genPair n
  , genTest "correct_scale" $
      do SW n <- genWidth
         B.correct_scale n <$> genBV n <*> B.genPair n
  , genTest "correct_mul" $
      do SW n <- genWidth
         B.correct_mul n <$> B.genPair n <*> B.genPair n
  , genTest "correct_mulPrecise" $
      do SW n <- genWidth
         B.correct_mulPrecise n <$> B.genPair n <*> B.genPair n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         B.correct_udiv n <$> B.genPair n <*> B.genPair n
  , genTest "correct_urem" $
      do SW n <- genWidth
         B.correct_urem n <$> B.genPair n <*> B.genPair n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         B.correct_sdiv n <$> B.genPair n <*> B.genPair n
  , genTest "correct_srem" $
      do SW n <- genWidth
         B.correct_srem n <$> B.genPair n <*> B.genPair n
  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         B.correct_udivSmtlib n <$> B.genPair n <*> B.genPair n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         B.correct_uremSmtlib n <$> B.genPair n <*> B.genPair n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         B.correct_sdivSmtlib n <$> B.genPair n <*> B.genPair n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         B.correct_sremSmtlib n <$> B.genPair n <*> B.genPair n
  , genTest "correct_udivPrecise" $
      do SW n <- genWidth
         B.correct_udivPrecise n <$> B.genPair n <*> B.genPair n
  , genTest "correct_uremPrecise" $
      do SW n <- genWidth
         B.correct_uremPrecise n <$> B.genPair n <*> B.genPair n
  ]

overallDomainTests :: TestTree
overallDomainTests = testGroup "Overall Domain"
  [ -- test that the union of consecutive singletons gives a precise interval
    genTest "singleton/union size" $
      do SW n <- genWidth
         let w =  maxUnsigned n
         x <- genBV n
         y <- min 1000 <$> genBV n
         let as = [ O.singleton n ((x + i) Bits..&. w) | i <- [0 .. y] ]
         let a = foldl1 O.join as
         pure $ property (O.size a == y + 1)
  , genTest "correct_bra1" $
      do SW n <- genWidth
         O.correct_bra1 n <$> genBV n <*> genBV n
  , genTest "correct_bra2" $
      do SW n <- genWidth
         O.correct_bra2 n <$> genBV n <*> genBV n <*> genBV n
  , genTest "correct_brb1" $
      do SW n <- genWidth
         O.correct_brb1 n <$> genBV n <*> genBV n <*> genBV n
  , genTest "correct_brb2" $
      do SW n <- genWidth
         O.correct_brb2 n <$> genBV n <*> genBV n <*> genBV n <*> genBV n
  , genTest "correct_any" $
      do SW n <- genWidth
         O.correct_any n <$> genBV n
  , genTest "correct_ubounds" $
      do SW n <- genWidth
         O.correct_ubounds n <$> O.genPair n
  , genTest "correct_sbounds" $
      do SW n <- genWidth
         O.correct_sbounds n <$> O.genPair n
  , genTest "correct_singleton" $
      do SW n <- genWidth
         O.correct_singleton n <$> genBV n <*> genBV n
  , genTest "correct_overlap" $
      do SW n <- genWidth
         O.correct_overlap <$> O.genDomain n <*> O.genDomain n <*> genBV n
  , genTest "precise_overlap" $
      do SW n <- genWidth
         O.precise_overlap <$> O.genDomain n <*> O.genDomain n
  , genTest "correct_asSingleton" $
      do SW n <- genWidth
         O.correct_asSingleton n <$> O.genDomain n
  , genTest "correct_mixed_domain_overlap" $
      do SW n <- genWidth
         O.correct_mixed_domain_overlap <$> A.genDomain n <*> B.genDomain n <*> genBV n
  , genTest "correct_mixed_domain_overlap_inv" $
      do SW n <- genWidth
         O.correct_mixed_domain_overlap_inv <$> A.genDomain n <*> B.genDomain n
  , genTest "correct_union" $
      do SW n <- genWidth
         O.correct_union n <$> O.genDomain n <*> O.genDomain n <*> genBV n
  , genTest "correct_join" $
      do SW n <- genWidth
         O.correct_join n <$> O.genDomain n <*> O.genDomain n <*> genBV n
  , genTest "correct_meet" $
      do SW n <- genWidth
         O.correct_meet <$> O.genDomain n <*> O.genDomain n <*> genBV n
  , genTest "correct_leq" $
      do SW n <- genWidth
         O.correct_leq <$> O.genDomain n <*> O.genDomain n <*> genBV n
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- O.genDomain w
                x <- O.genElement a
                pure $ O.correct_zero_ext w a u x
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- O.genDomain w
                x <- O.genElement a
                pure $ O.correct_sign_ext w a u x
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         O.correct_concat m <$> O.genPair m <*> pure n <*> O.genPair n
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure $ addIsLeq i_n z
         O.correct_select i n <$> O.genPair w
  , genTest "correct_add" $
      do SW n <- genWidth
         O.correct_add n <$> O.genPair n <*> O.genPair n
  , genTest "correct_neg" $
      do SW n <- genWidth
         O.correct_neg n <$> O.genPair n
  , genTest "correct_scale" $
      do SW n <- genWidth
         O.correct_scale n <$> genBV n <*> O.genPair n
  , genTest "correct_mul" $
      do SW n <- genWidth
         O.correct_mul n <$> O.genPair n <*> O.genPair n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         O.correct_udiv n <$> O.genPair n <*> O.genPair n
  , genTest "correct_urem" $
      do SW n <- genWidth
         O.correct_urem n <$> O.genPair n <*> O.genPair n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         O.correct_sdiv n <$> O.genPair n <*> O.genPair n
  , genTest "correct_srem" $
      do SW n <- genWidth
         O.correct_srem n <$> O.genPair n <*> O.genPair n
  , genTest "correct_shl" $
      do SW n <- genWidth
         O.correct_shl n <$> O.genPair n <*> O.genPair n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         O.correct_lshr n <$> O.genPair n <*> O.genPair n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         O.correct_ashr n <$> O.genPair n <*> O.genPair n
  , genTest "correct_rol" $
      do SW n <- genWidth
         O.correct_rol n <$> O.genPair n <*> O.genPair n
  , genTest "correct_ror" $
      do SW n <- genWidth
         O.correct_ror n <$> O.genPair n <*> O.genPair n
  , genTest "correct_eq" $
      do SW n <- genWidth
         O.correct_eq n <$> O.genPair n <*> O.genPair n
  , genTest "correct_ult" $
      do SW n <- genWidth
         O.correct_ult n <$> O.genPair n <*> O.genPair n
  , genTest "correct_slt" $
      do SW n <- genWidth
         O.correct_slt n <$> O.genPair n <*> O.genPair n
  , genTest "correct_not" $
      do SW n <- genWidth
         O.correct_not n <$> O.genPair n
  , genTest "correct_and" $
      do SW n <- genWidth
         O.correct_and n <$> O.genPair n <*> O.genPair n
  , genTest "correct_or" $
      do SW n <- genWidth
         O.correct_or n <$> O.genPair n <*> O.genPair n
  , genTest "correct_xor" $
      do SW n <- genWidth
         O.correct_xor n <$> O.genPair n <*> O.genPair n
  , genTest "correct_testBit" $
      do SW n <- genWidth
         i <- fromInteger <$> chooseInteger (0, intValue n - 1)
         O.correct_testBit n <$> O.genPair n <*> pure i
  , genTest "correct_popcnt" $
      do SW n <- genWidth
         O.correct_popcnt n <$> O.genPair n
  , genTest "correct_clz" $
      do SW n <- genWidth
         O.correct_clz n <$> O.genPair n
  , genTest "correct_ctz" $
      do SW n <- genWidth
         O.correct_ctz n <$> O.genPair n
  ]


transferTests :: TestTree
transferTests = testGroup "Transfer"
  [ genTest "correct_arithToBitwise" $
     do SW n <- genWidth
        O.correct_arithToBitwise n <$> A.genPair n
  , genTest "correct_bitwiseToArith" $
     do SW n <- genWidth
        O.correct_bitwiseToArith n <$> B.genPair n
  , genTest "correct_bitwiseToXorDomain" $
     do SW n <- genWidth
        O.correct_bitwiseToXorDomain n <$> B.genPair n
  , genTest "correct_arithToXorDomain" $
     do SW n <- genWidth
        O.correct_arithToXorDomain n <$> A.genPair n
  , genTest "correct_xorToBitwiseDomain" $
     do SW n <- genWidth
        O.correct_xorToBitwiseDomain n <$> X.genPair n
  , genTest "correct_asXorDomain" $
     do SW n <- genWidth
        O.correct_asXorDomain n <$> O.genPair n
  , genTest "correct_fromXorDomain" $
     do SW n <- genWidth
        O.correct_fromXorDomain n <$> X.genPair n
  ]

------------------------------------------------------------------------
-- Arithmetic Optimizations Tests

-- | Tests that optimized primop-based implementations match reference
-- loop-based implementations for ctz, clz, intLog2, and isPow2Integer.
arithmeticOptimiztionTests :: TestTree
arithmeticOptimiztionTests = testGroup "Arithmetic Optimizations"
  [ genTest "ctz: optimized matches reference" $
      do w <- chooseInt (1, 256)
         case someNat (fromIntegral w :: Natural) of
           Just (Some n)
             | Just LeqProof <- isPosNat n ->
                 do x <- chooseInteger (0, (2 ^ w) - 1)
                    pure $ BoolProperty $ ArithOpt.ctzOpt n x == ArithOpt.ctzRef n x
           _ -> error "test panic! ctz width"
  , genTest "clz: optimized matches reference" $
      do w <- chooseInt (1, 256)
         case someNat (fromIntegral w :: Natural) of
           Just (Some n)
             | Just LeqProof <- isPosNat n ->
                 do x <- chooseInteger (0, (2 ^ w) - 1)
                    pure $ BoolProperty $ ArithOpt.clzOpt n x == ArithOpt.clzRef n x
           _ -> error "test panic! clz width"
  , genTest "intLog2: optimized matches reference" $
      do x <- chooseInteger (1, 2 ^ (128 :: Int))
         pure $ BoolProperty $ ArithOpt.intLog2Opt x == ArithOpt.intLog2Ref x
  , genTest "isPow2Integer: optimized matches reference" $
      do x <- chooseInteger (0, 2 ^ (128 :: Int))
         pure $ BoolProperty $ ArithOpt.isPow2IntegerOpt x == ArithOpt.isPow2IntegerRef x
  ]
