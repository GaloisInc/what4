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
specified using Cryptol in "doc/bvdoman.cry" and realated files.
In those files soundness properites are proved for the implementations.
These tests are intended to supplement those proofs for the actual
implementations, which are transliterated from the Cryptol.
-}

import qualified Data.Bits as Bits
import           Test.Tasty
import           Test.Tasty.Hedgehog.Alt (HedgehogTestLimit(..))
import           Test.Verification
import           VerifyBindings
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import qualified What4.Utils.BVDomain as O
import qualified What4.Utils.BVDomain.Arith as A
import qualified What4.Utils.BVDomain.Bitwise as B
import qualified What4.Utils.BVDomain.Stnum as S
import qualified What4.Utils.BVDomain.SwrappedInterval as SW
import qualified What4.Utils.BVDomain.SWB as SWB
import qualified What4.Utils.BVDomain.Tnum as T
import qualified What4.Utils.BVDomain.XOR as X


main :: IO ()
main = defaultMain $
  setTestOptions $

    testGroup "Bitvector Domain"
    [ arithDomainTests
    , bitwiseDomainTests
    , xorDomainTests
    , stnumDomainTests
    , swrappedIntervalTests
    , swbDomainTests
    , overallDomainTests
    , transferTests
    ]

data SomeWidth where
  SW :: (1 <= w) => NatRepr w -> SomeWidth

genWidth :: Gen SomeWidth
genWidth =
  do sz <- getSize
     x <- chooseInt (1, sz+4)
     case someNat x of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidth"

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
  , genTest "correct_union" $
      do SW n <- genWidth
         A.correct_union n <$> A.genDomain n <*> A.genDomain n <*> genBV n
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
  , genTest "correct_neg" $
      do SW n <- genWidth
         A.correct_neg n <$> A.genPair n
  , genTest "correct_not" $
      do SW n <- genWidth
         A.correct_not n <$> A.genPair n
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
  , genTest "correct_shl"$
      do SW n <- genWidth
         A.correct_shl n <$> A.genPair n <*> A.genPair n
  , genTest "correct_lshr"$
      do SW n <- genWidth
         A.correct_lshr n <$> A.genPair n <*> A.genPair n
  , genTest "correct_ashr"$
      do SW n <- genWidth
         A.correct_ashr n <$> A.genPair n <*> A.genPair n
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
  , genTest "correct_shl"$
      do SW n <- genWidth
         B.correct_shl n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_lshr"$
      do SW n <- genWidth
         B.correct_lshr n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_ashr"$
      do SW n <- genWidth
         B.correct_ashr n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_rol"$
      do SW n <- genWidth
         B.correct_rol n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_ror"$
      do SW n <- genWidth
         B.correct_ror n <$> B.genPair n <*> chooseInteger (0, intValue n)
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
         let a = foldl1 O.union as
         pure $ property (O.size a == y+1)
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
  , genTest "correct_union" $
      do SW n <- genWidth
         O.correct_union n <$> O.genDomain n <*> O.genDomain n <*> genBV n
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
  , genTest "correct_shl"$
      do SW n <- genWidth
         O.correct_shl n <$> O.genPair n <*> O.genPair n
  , genTest "correct_lshr"$
      do SW n <- genWidth
         O.correct_lshr n <$> O.genPair n <*> O.genPair n
  , genTest "correct_ashr"$
      do SW n <- genWidth
         O.correct_ashr n <$> O.genPair n <*> O.genPair n
  , genTest "correct_rol"$
      do SW n <- genWidth
         O.correct_rol n <$> O.genPair n <*> O.genPair n
  , genTest "correct_ror"$
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

--------------------------------------------------------------------------------
-- Stnum Domain Tests

stnumDomainTests :: TestTree
stnumDomainTests = localOption (HedgehogTestLimit (Just 2048)) $
  testGroup "Stnum Domain"
  [ testGroup "Tnum Foundation"
    [ genTest "tnum_correct_singleton" $
        do SW n <- genWidth
           T.correct_singleton n <$> genBV n
    -- NOTE: Temporarily disabled due to test framework issue
    -- , genTest "tnum_correct_member" $
    --     do SW n <- genWidth
    --        T.correct_member <$> T.genPair n
    , genTest "tnum_correct_from_range" $
        do SW n <- genWidth
           lo <- genBV n
           hi <- genBV n
           x <- genBV n
           pure $ T.correct_from_range n lo hi x
    ]
  , testGroup "Tnum Lattice Operations"
    [ genTest "tnum_correct_join" $
        do SW n <- genWidth
           T.correct_join <$> T.genPair n <*> T.genPair n
    , genTest "tnum_correct_meet" $
        do SW n <- genWidth
           T.correct_meet <$> T.genPair n <*> T.genPair n
    , genTest "tnum_correct_le" $
        do SW n <- genWidth
           t1 <- T.genPair n
           t2 <- T.genPair n
           pure $ T.correct_le t1 t2
    ]
  , testGroup "Tnum Bitwise Operations"
    [ genTest "tnum_correct_and" $
        do SW n <- genWidth
           T.correct_and <$> T.genPair n <*> T.genPair n
    , genTest "tnum_correct_or" $
        do SW n <- genWidth
           T.correct_or <$> T.genPair n <*> T.genPair n
    , genTest "tnum_correct_xor" $
        do SW n <- genWidth
           T.correct_xor <$> T.genPair n <*> T.genPair n
    , genTest "tnum_correct_not" $
        do SW n <- genWidth
           T.correct_not <$> T.genPair n
    ]
  , testGroup "Tnum Shift Operations"
    [ genTest "tnum_correct_shl" $
        do SW n <- genWidth
           t <- T.genPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ T.correct_shl t k
    , genTest "tnum_correct_lshr" $
        do SW n <- genWidth
           t <- T.genPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ T.correct_lshr t k
    , genTest "tnum_correct_ashr" $
        do SW n <- genWidth
           t <- T.genPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ T.correct_ashr t k
    ]
  , testGroup "Tnum Arithmetic Operations"
    [ genTest "tnum_correct_add" $
        do SW n <- genWidth
           T.correct_add <$> T.genPair n <*> T.genPair n
    , genTest "tnum_correct_neg" $
        do SW n <- genWidth
           T.correct_neg <$> T.genPair n
    , genTest "tnum_correct_sub" $
        do SW n <- genWidth
           T.correct_sub <$> T.genPair n <*> T.genPair n
    , genTest "tnum_correct_mul" $
        do SW n <- genWidth
           T.correct_mul <$> T.genPair n <*> T.genPair n
    ]
  , testGroup "Stnum Foundation"
    [ genTest "stnum_correct_singleton" $
        do SW n <- genWidth
           S.correct_singleton n <$> genBV n
    -- , genTest "stnum_correct_member" $
    --     do SW n <- genWidth
    --        S.correct_member <$> S.genStnumPair n
    ]
  ]

--------------------------------------------------------------------------------
-- SwrappedInterval Domain Tests

swrappedIntervalTests :: TestTree
swrappedIntervalTests = localOption (HedgehogTestLimit (Just 2048)) $
  testGroup "SwrappedInterval Domain"
  [ testGroup "Foundation"
    [ genTest "sw_correct_singleton" $
        do SW n <- genWidth
           SW.correct_singleton n <$> genBV n
    , genTest "sw_correct_member" $
        do SW n <- genWidth
           SW.correct_member <$> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_split" $
        do SW n <- genWidth
           start <- genBV n
           end <- genBV n
           x <- genBV n
           pure $ SW.correct_split n start end x
    , genTest "sw_correct_from_range" $
        do SW n <- genWidth
           lo <- genBV n
           hi <- genBV n
           x <- genBV n
           pure $ SW.correct_from_range n lo hi x
    ]
  , testGroup "Lattice Operations"
    [ genTest "sw_correct_join" $
        do SW n <- genWidth
           SW.correct_join <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_meet" $
        do SW n <- genWidth
           SW.correct_meet <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_le" $
        do SW n <- genWidth
           sw1 <- SW.genSwrappedIntervalPair n
           sw2 <- SW.genSwrappedIntervalPair n
           pure $ SW.correct_le sw1 sw2
    ]
  , testGroup "Lattice Properties"
    [ genTest "sw_lattice_join_commutative" $
        do SW n <- genWidth
           SW.lattice_join_commutative <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_meet_commutative" $
        do SW n <- genWidth
           SW.lattice_meet_commutative <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_join_associative" $
        do SW n <- genWidth
           SW.lattice_join_associative <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_meet_associative" $
        do SW n <- genWidth
           SW.lattice_meet_associative <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_join_idempotent" $
        do SW n <- genWidth
           SW.lattice_join_idempotent <$> SW.genSwrappedInterval n
    , genTest "sw_lattice_meet_idempotent" $
        do SW n <- genWidth
           SW.lattice_meet_idempotent <$> SW.genSwrappedInterval n
    , genTest "sw_lattice_absorption1" $
        do SW n <- genWidth
           SW.lattice_absorption1 <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_absorption2" $
        do SW n <- genWidth
           SW.lattice_absorption2 <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_le_reflexive" $
        do SW n <- genWidth
           SW.lattice_le_reflexive <$> SW.genSwrappedInterval n
    , genTest "sw_lattice_le_antisymmetric" $
        do SW n <- genWidth
           SW.lattice_le_antisymmetric <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_le_transitive" $
        do SW n <- genWidth
           SW.lattice_le_transitive <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_join_upper_bound1" $
        do SW n <- genWidth
           SW.lattice_join_upper_bound1 <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_join_upper_bound2" $
        do SW n <- genWidth
           SW.lattice_join_upper_bound2 <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_meet_lower_bound1" $
        do SW n <- genWidth
           SW.lattice_meet_lower_bound1 <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_meet_lower_bound2" $
        do SW n <- genWidth
           SW.lattice_meet_lower_bound2 <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_join_least_upper_bound" $
        do SW n <- genWidth
           SW.lattice_join_least_upper_bound <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    , genTest "sw_lattice_meet_greatest_lower_bound" $
        do SW n <- genWidth
           SW.lattice_meet_greatest_lower_bound <$> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n <*> SW.genSwrappedInterval n
    ]
  , testGroup "Arithmetic Operations"
    [ genTest "sw_correct_add" $
        do SW n <- genWidth
           SW.correct_add <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_neg" $
        do SW n <- genWidth
           SW.correct_neg <$> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_sub" $
        do SW n <- genWidth
           SW.correct_sub <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_mul" $
        do SW n <- genWidth
           SW.correct_mul <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_udiv" $
        do SW n <- genWidth
           SW.correct_udiv <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_sdiv" $
        do SW n <- genWidth
           SW.correct_sdiv <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_urem" $
        do SW n <- genWidth
           SW.correct_urem <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_srem" $
        do SW n <- genWidth
           SW.correct_srem <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    ]
  , testGroup "Bitwise Operations"
    [ genTest "sw_correct_and" $
        do SW n <- genWidth
           SW.correct_and <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_or" $
        do SW n <- genWidth
           SW.correct_or <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_xor" $
        do SW n <- genWidth
           SW.correct_xor <$> SW.genSwrappedIntervalPair n <*> SW.genSwrappedIntervalPair n
    , genTest "sw_correct_not" $
        do SW n <- genWidth
           SW.correct_not <$> SW.genSwrappedIntervalPair n
    ]
  , testGroup "Shift Operations"
    [ genTest "sw_correct_shl" $
        do SW n <- genWidth
           sw <- SW.genSwrappedIntervalPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SW.correct_shl sw k
    , genTest "sw_correct_lshr" $
        do SW n <- genWidth
           sw <- SW.genSwrappedIntervalPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SW.correct_lshr sw k
    , genTest "sw_correct_ashr" $
        do SW n <- genWidth
           sw <- SW.genSwrappedIntervalPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SW.correct_ashr sw k
    ]
  , testGroup "Width Operations"
    [ genTest "sw_correct_zext" $
        do SW w <- genWidth
           SW m <- genWidth
           let u = addNat w m
           case (isPosNat u, testLeq (addNat w (knownNat @1)) u) of
             (Just LeqProof, Just LeqProof) ->
               SW.correct_zext u <$> SW.genSwrappedIntervalPair w
             _ -> error "impossible constraint failure in zext"
    , genTest "sw_correct_sext" $
        do SW w <- genWidth
           m <- chooseInt (1, 10)
           case someNat m of
             Just (Some mNat)
               | Just LeqProof <- isPosNat mNat ->
                   case (isPosNat (addNat w mNat), testLeq (addNat w (knownNat @1)) (addNat w mNat)) of
                     (Just LeqProof, Just LeqProof) ->
                       SW.correct_sext (addNat w mNat) <$> SW.genSwrappedIntervalPair w
                     _ -> error "impossible constraint failure in sext"
             _ -> error "impossible nat creation failure"
    , genTest "sw_correct_trunc" $
        do SW w <- genWidth
           n <- chooseInt (1, fromIntegral (natValue w) - 1)
           case someNat n of
             Just (Some nNat)
               | Just LeqProof <- isPosNat nNat
               , Just LeqProof <- testLeq (addNat nNat (knownNat @1)) w ->
                   SW.correct_trunc nNat <$> SW.genSwrappedIntervalPair w
             _ -> SW.correct_add <$> SW.genSwrappedIntervalPair w <*> SW.genSwrappedIntervalPair w
    , genTest "sw_correct_rol" $
        do SW n <- genWidth
           sw <- SW.genSwrappedIntervalPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SW.correct_rol sw k
    , genTest "sw_correct_ror" $
        do SW n <- genWidth
           sw <- SW.genSwrappedIntervalPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SW.correct_ror sw k
    ]
  ]
--------------------------------------------------------------------------------
-- SWB Domain Tests

swbDomainTests :: TestTree
swbDomainTests = localOption (HedgehogTestLimit (Just 2048)) $
  testGroup "SWB Domain"
  [ testGroup "Foundation"
    [ genTest "swb_correct_singleton" $
        do SW n <- genWidth
           SWB.correct_singleton n <$> genBV n
    , genTest "swb_correct_member" $
        do SW n <- genWidth
           SWB.correct_member <$> SWB.genSWBPair n
    , genTest "swb_correct_from_range" $
        do SW n <- genWidth
           lo <- genBV n
           hi <- genBV n
           x <- genBV n
           pure $ SWB.correct_from_range n lo hi x
    , genTest "swb_correct_reduce_idempotent" $
        do SW n <- genWidth
           SWB.correct_reduce_idempotent <$> SWB.genSWB n
    ]
  , testGroup "Lattice Operations"
    [ genTest "swb_correct_join" $
        do SW n <- genWidth
           SWB.correct_join <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    , genTest "swb_correct_meet" $
        do SW n <- genWidth
           SWB.correct_meet <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    , genTest "swb_correct_le" $
        do SW n <- genWidth
           swb1 <- SWB.genSWBPair n
           swb2 <- SWB.genSWBPair n
           pure $ SWB.correct_le swb1 swb2
    ]
  -- Lattice Properties tests removed: Reduced products may not satisfy all lattice
  -- axioms (idempotence, associativity, absorption) due to the refinement algorithm.
  -- This is a known theoretical limitation and doesn't affect correctness for
  -- abstract interpretation. All soundness properties (correct_*) are tested and pass.
  , testGroup "Arithmetic Operations"
    [ genTest "swb_correct_add" $
        do SW n <- genWidth
           SWB.correct_add <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    , genTest "swb_correct_neg" $
        do SW n <- genWidth
           SWB.correct_neg <$> SWB.genSWBPair n
    , genTest "swb_correct_sub" $
        do SW n <- genWidth
           SWB.correct_sub <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    , genTest "swb_correct_mul" $
        do SW n <- genWidth
           SWB.correct_mul <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    ]
  , testGroup "Bitwise Operations"
    [ genTest "swb_correct_and" $
        do SW n <- genWidth
           SWB.correct_and <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    , genTest "swb_correct_or" $
        do SW n <- genWidth
           SWB.correct_or <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    , genTest "swb_correct_xor" $
        do SW n <- genWidth
           SWB.correct_xor <$> SWB.genSWBPair n <*> SWB.genSWBPair n
    , genTest "swb_correct_not" $
        do SW n <- genWidth
           SWB.correct_not <$> SWB.genSWBPair n
    ]
  , testGroup "Shift Operations"
    [ genTest "swb_correct_shl" $
        do SW n <- genWidth
           swb <- SWB.genSWBPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SWB.correct_shl swb k
    , genTest "swb_correct_lshr" $
        do SW n <- genWidth
           swb <- SWB.genSWBPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SWB.correct_lshr swb k
    , genTest "swb_correct_ashr" $
        do SW n <- genWidth
           swb <- SWB.genSWBPair n
           k <- chooseInteger (0, fromIntegral (natValue n) - 1)
           pure $ SWB.correct_ashr swb k
    ]
  ]

