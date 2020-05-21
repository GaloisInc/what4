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
import           Test.Tasty.QuickCheck
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import qualified What4.Utils.BVDomain as O
import qualified What4.Utils.BVDomain.Arith as A
import qualified What4.Utils.BVDomain.Bitwise as B
import qualified What4.Utils.BVDomain.XOR as X


main :: IO ()
main = defaultMain $
  -- some tests discard a lot of values based on preconditions;
  -- this helps prevent those tests from failing for insufficent coverage
  localOption (QuickCheckMaxRatio 1000) $

  -- run at least 5000 tests
  adjustOption (\(QuickCheckTests x) -> QuickCheckTests (max x 5000)) $

    testGroup "Bitvector Domain"
    [ arithDomainTests
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
     x <- chooseInt (1, sz+4)
     case someNat x of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidth"

genBV :: NatRepr w -> Gen Integer
genBV w = chooseInteger (minUnsigned w, maxUnsigned w)

genTest :: String -> Gen Property -> TestTree
genTest nm p = testProperty nm p

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
