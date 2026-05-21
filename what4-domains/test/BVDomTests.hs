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
import qualified What4.Domains.BV.StridedInterval as SI
import qualified What4.Domains.BV.StridedInterval.Internal as SI.I
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
    , stridedIntervalDomainTests
    , stridedIntervalVsArithTests
    , stridedIntervalInternalTests
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

stridedIntervalDomainTests :: TestTree
stridedIntervalDomainTests =
  testGroup "Strided Interval Domain"
  -- Invariant postconditions: every operation preserves 'proper'.
  [ genTest "correct_proper_bottom" $
      do SW n <- genWidth
         pure (SI.correct_proper_bottom n)
  , genTest "correct_proper_top" $
      do SW n <- genWidth
         pure (SI.correct_proper_top n)
  , genTest "correct_proper_singleton" $
      do SW n <- genWidth
         SI.correct_proper_singleton n <$> genBV n
  , genTest "correct_proper_mkStridedInterval" $
      do SW n <- genWidth
         SI.correct_proper_mkStridedInterval n
           <$> chooseBool <*> genBV n <*> genBV n <*> genBV n
  , genTest "correct_proper_range" $
      do SW n <- genWidth
         SI.correct_proper_range n <$> genBV n <*> genBV n
  , genTest "correct_proper_fromAscEltList" $
      do SW n <- genWidth
         do k <- chooseInt (0, 8)
            xs <- traverse (const (genBV n)) [1..k]
            pure (SI.correct_proper_fromAscEltList n xs)
  , genTest "correct_proper_join" $
      do SW n <- genWidth
         SI.correct_proper_join <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_unionSingleton" $
      do SW n <- genWidth
         SI.correct_proper_unionSingleton <$> SI.genDomain n <*> genBV n
  , genTest "correct_proper_glb" $
      do SW n <- genWidth
         SI.correct_proper_glb <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_add" $
      do SW n <- genWidth
         SI.correct_proper_add <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_adc" $
      do SW n <- genWidth
         carry <- chooseInt (0, 2)
         let c = case carry of 0 -> Nothing; 1 -> Just False; _ -> Just True
         SI.correct_proper_adc <$> SI.genDomain n <*> SI.genDomain n <*> pure c
  , genTest "correct_proper_mul" $
      do SW n <- genWidth
         SI.correct_proper_mul <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_sub" $
      do SW n <- genWidth
         SI.correct_proper_sub <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_negate" $
      do SW n <- genWidth
         SI.correct_proper_negate <$> SI.genDomain n
  , genTest "correct_proper_scale" $
      do SW n <- genWidth
         SI.correct_proper_scale <$> genBV n <*> SI.genDomain n
  , genTest "correct_proper_not" $
      do SW n <- genWidth
         SI.correct_proper_not <$> SI.genDomain n
  , genTest "correct_proper_and" $
      do SW n <- genWidth
         SI.correct_proper_and <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_or" $
      do SW n <- genWidth
         SI.correct_proper_or <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_xor" $
      do SW n <- genWidth
         SI.correct_proper_xor <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_shl" $
      do SW n <- genWidth
         SI.correct_proper_shl n <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_lshr" $
      do SW n <- genWidth
         SI.correct_proper_lshr n <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_ashr" $
      do SW n <- genWidth
         SI.correct_proper_ashr n <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_rol" $
      do SW n <- genWidth
         SI.correct_proper_rol n <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_ror" $
      do SW n <- genWidth
         SI.correct_proper_ror n <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_udiv" $
      do SW n <- genWidth
         SI.correct_proper_udiv <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_urem" $
      do SW n <- genWidth
         SI.correct_proper_urem <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_sdiv" $
      do SW n <- genWidth
         SI.correct_proper_sdiv n <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_srem" $
      do SW n <- genWidth
         SI.correct_proper_srem n <$> SI.genDomain n <*> SI.genDomain n
  , genTest "correct_proper_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         SI.correct_proper_concat m <$> SI.genDomain m <*> pure n <*> SI.genDomain n
  , genTest "correct_proper_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure $ addIsLeq i_n z
         SI.correct_proper_select i n <$> SI.genDomain w
  , genTest "correct_proper_trunc" $
      do SW n <- genWidth
         SW m <- genWidth
         let w = addNat n m
         LeqProof <- pure $ addIsLeq n m
         SI.correct_proper_trunc n <$> SI.genDomain w
  , genTest "correct_proper_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- SI.genDomain w
                pure (SI.correct_proper_zext a u)
  , genTest "correct_proper_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- SI.genDomain w
                pure (SI.correct_proper_sext w a u)

  -- Predicates.
  , genTest "correct_toList_member" $
      do SW n <- genWidth
         SI.correct_toList_member <$> SI.genDomain n
  , genTest "correct_member_toList" $
      do SW n <- genWidth
         SI.correct_member_toList <$> SI.genDomain n <*> genBV n
  , genTest "correct_asSingleton" $
      do SW n <- genWidth
         SI.correct_asSingleton <$> SI.genDomain n
  , genTest "correct_domainsOverlap" $
      do SW n <- genWidth
         SI.correct_domainsOverlap <$> SI.genDomain n <*> SI.genDomain n <*> genBV n
  , genTest "correct_domainsOverlap_bottom" $
      do SW n <- genWidth
         SI.correct_domainsOverlap_bottom <$> SI.genDomain n

  -- Lattice operations.
  , genTest "correct_join" $
      do SW n <- genWidth
         SI.correct_join <$> SI.genDomain n <*> SI.genDomain n <*> genBV n
  , genTest "correct_meet" $
      do SW n <- genWidth
         SI.correct_meet <$> SI.genDomain n <*> SI.genDomain n <*> genBV n
  , genTest "correct_leq" $
      do SW n <- genWidth
         SI.correct_leq <$> SI.genDomain n <*> SI.genDomain n <*> genBV n
  , genTest "correct_unionSingleton" $
      do SW n <- genWidth
         SI.correct_unionSingleton <$> SI.genDomain n <*> genBV n
  , genTest "correct_glb" $
      do SW n <- genWidth
         SI.correct_glb <$> SI.genDomain n <*> SI.genDomain n <*> genBV n
  , genTest "correct_glb_singleton_left" $
      do SW n <- genWidth
         SI.correct_glb_singleton_left n <$> genBV n <*> SI.genDomain n
  , genTest "correct_glb_singleton_right" $
      do SW n <- genWidth
         SI.correct_glb_singleton_right n <$> genBV n <*> SI.genDomain n

  -- Lattice laws.
  , genTest "join_commutative" $
      do SW n <- genWidth
         SI.join_commutative <$> SI.genDomain n <*> SI.genDomain n <*> genBV n
  , genTest "join_idempotent" $
      do SW n <- genWidth
         SI.join_idempotent <$> SI.genDomain n <*> genBV n
  , genTest "meet_commutative" $
      do SW n <- genWidth
         SI.meet_commutative <$> SI.genDomain n <*> SI.genDomain n <*> genBV n
  , genTest "meet_idempotent" $
      do SW n <- genWidth
         SI.meet_idempotent <$> SI.genDomain n <*> genBV n
  , genTest "join_top" $
      do SW n <- genWidth
         SI.join_top n <$> SI.genDomain n <*> genBV n
  , genTest "join_bottom" $
      do SW n <- genWidth
         SI.join_bottom n <$> SI.genDomain n <*> genBV n
  , genTest "meet_top" $
      do SW n <- genWidth
         SI.meet_top n <$> SI.genDomain n <*> genBV n
  , genTest "meet_bottom" $
      do SW n <- genWidth
         SI.meet_bottom n <$> SI.genDomain n <*> genBV n
  , genTest "leq_reflexive" $
      do SW n <- genWidth
         SI.leq_reflexive <$> SI.genDomain n
  , genTest "join_upper_bound" $
      do SW n <- genWidth
         SI.join_upper_bound <$> SI.genDomain n <*> SI.genDomain n
  , genTest "join_proper" $
      do SW n <- genWidth
         SI.join_proper <$> SI.genDomain n <*> SI.genDomain n
  , genTest "meet_proper" $
      do SW n <- genWidth
         SI.meet_proper <$> SI.genDomain n <*> SI.genDomain n

  -- Width manipulation.
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         SI.correct_concat m <$> SI.genPair m <*> pure n <*> SI.genPair n
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure $ addIsLeq i_n z
         SI.correct_select i n <$> SI.genPair w
  , genTest "correct_trunc" $
      do SW n <- genWidth
         SW m <- genWidth
         let w = addNat n m
         LeqProof <- pure $ addIsLeq n m
         SI.correct_trunc n <$> SI.genPair w
  , genTest "correct_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- SI.genDomain w
                x <- SI.genElement a
                pure (SI.correct_zext a u x)
  , genTest "correct_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do a <- SI.genDomain w
                x <- SI.genElement a
                pure (SI.correct_sext w a u x)

  -- Arithmetic.
  , genTest "correct_add" $
      do SW n <- genWidth
         SI.correct_add n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_adc" $
      do SW n <- genWidth
         SI.correct_adc n <$> SI.genPair n <*> SI.genPair n <*> chooseBool
  , genTest "correct_sub" $
      do SW n <- genWidth
         SI.correct_sub n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_negate" $
      do SW n <- genWidth
         SI.correct_negate n <$> SI.genPair n
  , genTest "correct_scale" $
      do SW n <- genWidth
         SI.correct_scale n <$> genBV n <*> SI.genPair n
  , genTest "correct_mul" $
      do SW n <- genWidth
         SI.correct_mul n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         SI.correct_udiv n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_urem" $
      do SW n <- genWidth
         SI.correct_urem n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         SI.correct_sdiv n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_srem" $
      do SW n <- genWidth
         SI.correct_srem n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_not" $
      do SW n <- genWidth
         SI.correct_not n <$> SI.genPair n
  , genTest "correct_and" $
      do SW n <- genWidth
         SI.correct_and n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_or" $
      do SW n <- genWidth
         SI.correct_or n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_xor" $
      do SW n <- genWidth
         SI.correct_xor n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_shl" $
      do SW n <- genWidth
         SI.correct_shl n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         SI.correct_lshr n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         SI.correct_ashr n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_rol" $
      do SW n <- genWidth
         SI.correct_rol n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_ror" $
      do SW n <- genWidth
         SI.correct_ror n <$> SI.genPair n <*> SI.genPair n

  -- Destructors.
  , genTest "correct_size" $
      do SW n <- genWidth
         SI.correct_size <$> SI.genPair n
  , genTest "correct_ubounds" $
      do SW n <- genWidth
         SI.correct_ubounds <$> SI.genDomain n <*> genBV n
  , genTest "correct_ubounds_bottom" $
      do SW n <- genWidth
         pure (SI.correct_ubounds_bottom n)
  , genTest "correct_sbounds" $
      do SW n <- genWidth
         SI.correct_sbounds n <$> SI.genPair n
  , genTest "correct_bitbounds" $
      do SW n <- genWidth
         SI.correct_bitbounds n <$> SI.genPair n
  , genTest "correct_unknowns" $
      do SW n <- genWidth
         a <- SI.genDomain n
         x <- SI.genElement a
         y <- SI.genElement a
         pure (SI.correct_unknowns n a x y)
  , genTest "correct_eq" $
      do SW n <- genWidth
         SI.correct_eq n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_ult" $
      do SW n <- genWidth
         SI.correct_ult n <$> SI.genPair n <*> SI.genPair n
  , genTest "correct_slt" $
      do SW n <- genWidth
         SI.correct_slt n <$> SI.genPair n <*> SI.genPair n

  -- Bottom edge cases.
  , genTest "correct_glb_bottom_left" $
      do SW n <- genWidth
         SI.correct_glb_bottom_left <$> SI.genDomain n
  , genTest "correct_glb_bottom_right" $
      do SW n <- genWidth
         SI.correct_glb_bottom_right <$> SI.genDomain n
  , genTest "correct_add_bottom_left" $
      do SW n <- genWidth
         SI.correct_add_bottom_left n <$> SI.genDomain n
  , genTest "correct_add_bottom_right" $
      do SW n <- genWidth
         SI.correct_add_bottom_right n <$> SI.genDomain n
  , genTest "correct_mul_bottom_left" $
      do SW n <- genWidth
         SI.correct_mul_bottom_left n <$> SI.genDomain n
  , genTest "correct_mul_bottom_right" $
      do SW n <- genWidth
         SI.correct_mul_bottom_right n <$> SI.genDomain n

  -- Algebraic justifications of the size-cap invariant. The size cap
  -- @(r + 1) * s <= m@ is a sufficient condition for the residues
  -- @(b + i * s) mod m@ for @0 <= i <= r@ to be pairwise distinct, and
  -- under that cap the simple `member` formula matches the defining set.
  , genTest "correct_size_cap_sufficient" $
      do b <- chooseInteger (-(2 ^ (12 :: Int)), 2 ^ (12 :: Int))
         r <- chooseInteger (0, 64)
         s <- chooseInteger (1, 64)
         w <- chooseInteger (0, 12)
         pure (sizeCapSufficient b r s w)
  , genTest "correct_size_cap_simple_member" $
      do b <- chooseInteger (-(2 ^ (8 :: Int)), 2 ^ (8 :: Int))
         r <- chooseInteger (0, 64)
         s <- chooseInteger (1, 64)
         w <- chooseInteger (1, 8)
         x <- chooseInteger (-(2 ^ (8 :: Int)), 2 ^ (8 :: Int))
         pure (sizeCapSimpleMember b r s w x)
  ]
  where
    sizeCapSufficient bRaw rRaw sRaw wRaw =
      property $
        let r = abs rRaw
            s = max 1 (abs sRaw)
            w_bits = abs wRaw `mod` 12
            m = 2 ^ w_bits
            b = bRaw `mod` max 1 m
            residues = [ (b + i * s) `mod` m | i <- [0 .. r] ]
        in (r + 1) * s > m
           || length residues == length (uniq residues)
      where
        uniq []     = []
        uniq (x:xs) = x : uniq [ y | y <- xs, y /= x ]
    sizeCapSimpleMember bRaw rRaw sRaw wRaw xRaw =
      property $
        let r = abs rRaw
            s = max 1 (abs sRaw)
            w_bits = max 1 (abs wRaw `mod` 8)
            m = 2 ^ w_bits
            b = bRaw `mod` m
            x = xRaw `mod` m
            d = (x - b) `mod` m
            viaFormula = d `mod` s == 0 && d `div` s <= r
            viaSet     = elem x [ (b + i * s) `mod` m | i <- [0 .. r] ]
        in (r + 1) * s > m || viaFormula == viaSet

-- | Differential tests against 'A.Domain'. Inputs are sampled across
-- /any-stride/ SIs ('SI.genDomain') so the general algorithms are
-- actually exercised; 'SI.toArith' coarsens an SI to its contiguous
-- unsigned cover, which is the natural common ground with 'A.Domain'.
--
-- Two flavors of comparison appear below:
--
--   * /Precision/: every concrete value @x@ accepted by 'SI.op' is
--     also accepted by 'A.op' on the cover inputs. Pins down "SI is at
--     least as precise as A on this op" while allowing strict
--     refinement. Tested pointwise (via 'SI.member' ⇒ 'A.member')
--     because 'SI.toArith' is lossy on stride > 1 outputs (it picks a
--     contiguous cover that can be a strictly looser shape than what
--     'A.op' produces, even though SI's actual set is tighter).
--   * /Equality/: SI's result equals 'SI.fromArith' of Arith's result.
--     Used for ops where SI's algorithm is just a re-routing through
--     'A.op' on the cover (no refinement possible).
--
-- Ops that may produce a strided refinement go in the precision group;
-- ops that route through 'A.op' verbatim go in the equality group.
-- Soundness ('A.member x ⇒ SI.member x' under concrete operations) is
-- not tested here; that's covered by 'correct_*' in
-- 'stridedIntervalDomainTests'.
stridedIntervalVsArithTests :: TestTree
stridedIntervalVsArithTests =
  testGroup "Strided Interval vs. Arith"
  -- Round-trip: stride-1 SI ↔ Arith preserves membership.
  [ genTest "arith->si->arith" $
      do SW n <- genWidth
         a <- A.genDomain n
         x <- genBV n
         pure $ property
           (A.member a x == A.member (SI.toArith (SI.fromArith (maxUnsigned n) a)) x)

  -- Bounds (definitionally cover bounds — exact equality).
  , genTest "ubounds" $
      do SW n <- genWidth
         a <- SI.genDomain n
         pure $ nonBottom1 a $ SI.ubounds a == A.ubounds (SI.toArith a)
  , genTest "sbounds" $
      do SW n <- genWidth
         a <- SI.genDomain n
         pure $ nonBottom1 a $ SI.sbounds n a == A.sbounds n (SI.toArith a)

  -- Precision: every member of SI's result is a member of A's result
  -- on the cover (pointwise SI.member ⇒ A.member).
  , genTest "add" $ precisionBin SI.add A.add
  , genTest "sub" $ precisionBin SI.sub (\x y -> A.add x (A.negate y))
  , genTest "mul" $ precisionBin SI.mul A.mul
  , genTest "scale" $
      do SW n <- genWidth
         k <- genBV n
         a <- SI.genDomain n
         x <- genBV n
         pure $ Prelude.not (SI.isBottom a) ==>
           SI.member (SI.scale k a) x ==>
             A.member (A.scale (toSigned n k) (SI.toArith a)) x
  , genTest "negate" $
      do SW n <- genWidth
         a <- SI.genDomain n
         x <- genBV n
         pure $ Prelude.not (SI.isBottom a) ==>
           SI.member (SI.negate a) x ==> A.member (A.negate (SI.toArith a)) x
  , genTest "not" $
      do SW n <- genWidth
         a <- SI.genDomain n
         x <- genBV n
         pure $ Prelude.not (SI.isBottom a) ==>
           SI.member (SI.not a) x ==> A.member (A.not (SI.toArith a)) x
  , genTest "shl" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         x <- genBV n
         pure $ Prelude.not (SI.isBottom a || SI.isBottom b) ==>
           SI.member (SI.shl n a b) x ==>
             A.member (A.shl n (SI.toArith a) (SI.toArith b)) x

  -- Equality: SI re-routes through A.op on the cover, so equality
  -- after fromArith must hold. Bottom inputs are excluded — SI
  -- propagates them explicitly while Arith doesn't, and we already
  -- test bottom propagation in 'correct_*_bottom_*' soundness tests.
  , genTest "lshr" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         x <- genBV n
         -- SI.lshr can preserve stride when the shift is a singleton
         -- and the operand's stride is divisible by 2^k; precision
         -- check rather than equality.
         pure $ Prelude.not (SI.isBottom a || SI.isBottom b) ==>
           SI.member (SI.lshr n a b) x ==>
             A.member (A.lshr n (SI.toArith a) (SI.toArith b)) x
  , genTest "ashr" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         pure $ nonBottom2 a b $
           SI.ashr n a b == SI.fromArith (maxUnsigned n) (A.ashr n (SI.toArith a) (SI.toArith b))
  , genTest "udiv" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         pure $ nonBottom2 a b $
           SI.udiv a b == SI.fromArith (maxUnsigned n) (A.udiv (SI.toArith a) (SI.toArith b))
  , genTest "urem" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         pure $ nonBottom2 a b $
           SI.urem a b == SI.fromArith (maxUnsigned n) (A.urem (SI.toArith a) (SI.toArith b))
  , genTest "sdiv" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         pure $ nonBottom2 a b $
           SI.sdiv n a b == SI.fromArith (maxUnsigned n) (A.sdiv n (SI.toArith a) (SI.toArith b))
  , genTest "srem" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         pure $ nonBottom2 a b $
           SI.srem n a b == SI.fromArith (maxUnsigned n) (A.srem n (SI.toArith a) (SI.toArith b))
  , genTest "meet" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         x <- genBV n
         -- 'meet' produces a sound /over/-approximation. SI's meet
         -- can refine to a stride > 1 shape (e.g. when both inputs
         -- have the same strided shape), so only the precision
         -- direction is checked: every member of SI's meet is a
         -- member of A's meet on the covers.
         pure $ Prelude.not (SI.isBottom a || SI.isBottom b) ==>
           SI.member (SI.meet a b) x ==>
             A.member (A.meet (SI.toArith a) (SI.toArith b)) x
  , genTest "sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof -> do
             (a, _) <- SI.genPair w
             y <- SI.genElement (SI.sext w a u)
             -- SI.sext preserves stride (e.g. {0, 4} sign-extended to
             -- a wider width stays {0, 4} stride-4); the contiguous
             -- Arith cover is strictly looser, so we test that every
             -- member of SI's sext result lies in Arith's sext result.
             pure $ Prelude.not (SI.isBottom a) ==>
               A.member (A.sext w (SI.toArith a) u) y
  , genTest "concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- SI.genDomain m
         b <- SI.genDomain n
         x <- chooseInteger (0, maxUnsigned (addNat m n))
         -- SI.concat preserves stride when one operand is a singleton,
         -- which gives a strictly more precise result than the cover.
         pure $ Prelude.not (SI.isBottom a || SI.isBottom b) ==>
           SI.member (SI.concat m a n b) x ==>
             A.member (A.concat m (SI.toArith a) n (SI.toArith b)) x
  , genTest "select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure $ addIsLeq i_n z
         a <- SI.genDomain w
         pure $ nonBottom1 a $
           SI.select i n a == SI.fromArith (maxUnsigned n) (A.select i n (SI.toArith a))
  , genTest "zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof -> do
             a <- SI.genDomain w
             y <- SI.genElement (SI.zext a u)
             -- SI.zext preserves stride (e.g. {0, 2} zero-extended to
             -- a wider width stays {0, 2} stride-2); precision check.
             pure $ Prelude.not (SI.isBottom a) ==>
               A.member (A.zext (SI.toArith a) u) y
  , genTest "range" $
      do SW n <- genWidth
         lo <- genBV n
         hi <- genBV n
         pure $ property (SI.range n lo hi == SI.fromArith (maxUnsigned n) (A.range n lo hi))
  , genTest "fromAscEltList" $
      do SW n <- genWidth
         lo <- chooseInteger (0, maxUnsigned n)
         let maxK = max 0 (maxUnsigned n - lo)
         k  <- chooseInteger (0, min maxK (intValue n))
         let xs = [ lo + i | i <- [0 .. k] ]
         pure $ property
           (SI.fromAscEltList n xs == SI.fromArith (maxUnsigned n) (A.fromAscEltList n xs))

  -- Predicate agreement on stride-1 inputs (where SI and A have
  -- identical information). Uses 'SI.genDomain' (size-bounded) and
  -- filters to stride 1 — 'A.genDomain' picks @siRange@ up to the full
  -- @2^w - 1@, which makes 'leq's enumeration blow up at large widths.
  , genTest "leq" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         pure $ (SI.stride a == 1 && SI.stride b == 1) ==>
                  (SI.leq a b == A.leq (SI.toArith a) (SI.toArith b))
  , genTest "domainsOverlap" $
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         pure $ (SI.stride a == 1 && SI.stride b == 1) ==>
                  (SI.domainsOverlap a b == A.domainsOverlap (SI.toArith a) (SI.toArith b))
  ]
  where
    precisionBin
      :: (forall w. (1 <= w) => SI.StridedInterval w -> SI.StridedInterval w -> SI.StridedInterval w)
      -> (forall w. (1 <= w) => A.Domain w -> A.Domain w -> A.Domain w)
      -> Gen Property
    precisionBin siOp aOp =
      do SW n <- genWidth
         a <- SI.genDomain n
         b <- SI.genDomain n
         x <- genBV n
         pure $ Prelude.not (SI.isBottom a || SI.isBottom b) ==>
           SI.member (siOp a b) x ==>
             A.member (aOp (SI.toArith a) (SI.toArith b)) x

    nonBottom1 :: SI.StridedInterval w -> Bool -> Property
    nonBottom1 a = (Prelude.not (SI.isBottom a) ==>)

    nonBottom2 :: SI.StridedInterval w -> SI.StridedInterval w' -> Bool -> Property
    nonBottom2 a b = (Prelude.not (SI.isBottom a || SI.isBottom b) ==>)


-- | Direct property tests for the internal helpers underlying
-- 'SI.glb'\'s Diophantine path. These pin down the algebraic spec of
-- 'eGCD', 'ceilDivPos'/'floorDivPos', and 'solveLinearDiophantine'
-- itself, which 'correct_glb' cannot exercise directly because it only
-- checks the @member x (glb a b) ⇒ member x a && member x b@ direction.
stridedIntervalInternalTests :: TestTree
stridedIntervalInternalTests =
  testGroup "Strided Interval Internal"
  [ testGroup "eGCD"
    [ genTest "Bezout identity" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, n, m) = SI.I.eGCD a b
           pure (property (n * a + m * b == g))
    , genTest "g is nonnegative" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, _, _) = SI.I.eGCD a b
           pure (property (g >= 0))
    , genTest "g divides both inputs" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, _, _) = SI.I.eGCD a b
           pure $ property $
             if g == 0
               then a == 0 && b == 0
               else a `mod` g == 0 && b `mod` g == 0
    , genTest "matches Prelude.gcd" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, _, _) = SI.I.eGCD a b
           pure (property (g == gcd a b))
    ]
  , testGroup "ceilDivPos / floorDivPos"
    [ genTest "ceilDivPos bounds" $
        do x <- chooseInteger (-1024, 1024)
           y <- chooseInteger (1, 2 ^ (32 :: Int))
           let q = SI.I.ceilDivPos x y
           -- q is the least integer with q * y >= x
           pure (property (q * y >= x && (q - 1) * y < x))
    , genTest "floorDivPos bounds" $
        do x <- chooseInteger (-1024, 1024)
           y <- chooseInteger (1, 2 ^ (32 :: Int))
           let q = SI.I.floorDivPos x y
           -- q is the greatest integer with q * y <= x
           pure (property (q * y <= x && (q + 1) * y > x))
    ]
  , testGroup "solveLinearDiophantine"
    -- Soundness: construct the input from a known solution, so the
    -- solver must succeed; check the returned (x, y) satisfies the
    -- equation and stays within bounds.
    [ genTest "sound" $
        do a    <- chooseInteger (1, 2 ^ (32 :: Int))
           b    <- chooseInteger (1, 2 ^ (32 :: Int))
           aMax <- chooseInteger (1, 2 ^ (32 :: Int))
           bMax <- chooseInteger (1, 2 ^ (32 :: Int))
           x0   <- chooseInteger (0, aMax)
           y0   <- chooseInteger (0, bMax)
           let c = a * x0 - b * y0
           pure $ (c /= 0) ==>
             case SI.I.solveLinearDiophantine a b c aMax bMax of
               Nothing     -> property False
               Just (x, y) ->
                 property (0 <= x && x <= aMax
                        && 0 <= y && y <= bMax
                        && a * x - b * y == c)
    -- Completeness on small inputs: brute-force over [0..aMax]×[0..bMax]
    -- to see if a solution exists, then check that the solver's verdict
    -- agrees.
    , genTest "complete (brute-force)" $
        do a    <- chooseInteger (1, 64)
           b    <- chooseInteger (1, 64)
           aMax <- chooseInteger (1, 64)
           bMax <- chooseInteger (1, 64)
           cAbs <- chooseInteger (1, 64)
           sign <- chooseBool
           let c = if sign then cAbs else -cAbs
               exists = or [ a * x - b * y == c
                           | x <- [0 .. aMax], y <- [0 .. bMax]
                           ]
           pure $ property $
             case (exists, SI.I.solveLinearDiophantine a b c aMax bMax) of
               (True,  Just _ ) -> True
               (False, Nothing) -> True
               _                -> False
    -- Specific shape that must succeed: a*k - 1*0 = a*k.
    , genTest "finds endpoint intersection" $
        do a <- chooseInteger (1, 2 ^ (32 :: Int))
           k <- chooseInteger (1, 2 ^ (32 :: Int))
           let aMax = k
               bMax = 1
               c    = a * k
           pure $ property $
             case SI.I.solveLinearDiophantine a 1 c aMax bMax of
               Just _  -> True
               Nothing -> False
    ]
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
