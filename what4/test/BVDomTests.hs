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

import           Test.Tasty
import           Test.Tasty.QuickCheck
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import qualified What4.Utils.BVDomain.Arith as A
import qualified What4.Utils.BVDomain.Bitwise as B

main :: IO ()
main = defaultMain $
  localOption (QuickCheckTests 5000) $
    testGroup "Bitvector Domain"
    [ arithDomainTests
    , bitwiseDomainTests
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
       _ -> fail "test panic! genWidth"

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
         A.correct_union <$> A.genDomain n <*> A.genDomain n <*> genBV n
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
         A.correct_shrink i <$> A.genPair (addNat i n)
  , genTest "correct_trunc" $
      do SW n <- genWidth
         SW m <- genWidth
         let w = addNat n m
         LeqProof <- pure $ addIsLeq n m
         A.correct_trunc n <$> A.genPair w
  , genTest "correct_add" $
      do SW n <- genWidth
         A.correct_add <$> A.genPair n <*> A.genPair n
  , genTest "correct_neg" $
      do SW n <- genWidth
         A.correct_neg <$> A.genPair n
  , genTest "correct_not" $
      do SW n <- genWidth
         A.correct_not <$> A.genPair n
  , genTest "correct_mul" $
      do SW n <- genWidth
         A.correct_mul <$> A.genPair n <*> A.genPair n
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

bitwiseDomainTests :: TestTree
bitwiseDomainTests = localOption (QuickCheckMaxRatio 1000) $
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
         pure $ B.correct_union a b x
  , genTest "correct_union2" $
      do SW n <- genWidth
         a <- B.genDomain n
         (b,x) <- B.genPair n
         pure $ B.correct_union a b x
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
         B.correct_shrink i <$> B.genPair (addNat i n)
  , genTest "correct_trunc" $
      do SW n <- genWidth
         SW m <- genWidth
         let w = addNat n m
         LeqProof <- pure $ addIsLeq n m
         B.correct_trunc n <$> B.genPair w
  , genTest "correct_shl"$
      do SW n <- genWidth
         B.correct_shl n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_lshr"$
      do SW n <- genWidth
         B.correct_lshr n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_ashr"$
      do SW n <- genWidth
         B.correct_ashr n <$> B.genPair n <*> chooseInteger (0, intValue n)
  , genTest "correct_eq" $
      do SW n <- genWidth
         B.correct_eq n <$> B.genPair n <*> B.genPair n
  , genTest "correct_not" $
      do SW n <- genWidth
         B.correct_not <$> B.genPair n
  , genTest "correct_and" $
      do SW n <- genWidth
         B.correct_and <$> B.genPair n <*> B.genPair n
  , genTest "correct_or" $
      do SW n <- genWidth
         B.correct_or <$> B.genPair n <*> B.genPair n
  , genTest "correct_xor" $
      do SW n <- genWidth
         B.correct_xor <$> B.genPair n <*> B.genPair n
  , genTest "correct_testBit" $
      do SW n <- genWidth
         i <- fromInteger <$> chooseInteger (0, intValue n - 1)
         B.correct_testBit n <$> B.genPair n <*> pure i
  ]
