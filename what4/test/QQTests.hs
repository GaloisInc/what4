-----------------------------------------------------------------------
-- |
-- Module           : Main
-- Description      : Tests for the What4 quasiquoters
-- Copyright        : (c) Galois, Inc 2026
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- Tests for "What4.QQ". Two groups:
--
--  * /behavior/: quoted terms build the expected 'SymExpr's, checked by
--    concrete evaluation (the 'ExprBuilder' constant-folds these, so no
--    solver is needed) and, for bitvectors, by a static width assertion
--    ('hasWidth').
--
--  * /snapshot/: the literal Haskell code produced by the quasiquoter,
--    obtained via 'dumpW4', compared against golden files. Regenerate with
--    @cabal test what4:exprs_tests --test-options=--accept@.
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module QQTests (tests) where

import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString.Lazy.Char8 as BSL
import           Data.Parameterized.NatRepr (NatRepr, knownNat)
import           Data.Parameterized.Nonce (withIONonceGenerator)
import           Data.Ratio ((%))

import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Golden (goldenVsString)
import           Test.Tasty.HUnit (testCase, (@?=))

import           What4.Expr
                   ( ExprBuilder, EmptyExprBuilderState(EmptyExprBuilderState)
                   , newExprBuilder, FloatModeRepr(FloatIEEERepr), Flags, FloatIEEE )
import           What4.Interface (SymBV, asBV, asInteger, asRational, asConstantPred, bvLit)
import           What4.QQ (w4, dumpW4)

type Sym t = ExprBuilder t EmptyExprBuilderState (Flags FloatIEEE)

withSym :: (forall t. Sym t -> IO a) -> IO a
withSym k = withIONonceGenerator $ \ng ->
  k =<< newExprBuilder FloatIEEERepr EmptyExprBuilderState ng

-- | Statically assert a bitvector's width (without having to name the
-- backend's phantom type parameter). A width mismatch is a type error. The
-- @sym@ argument (ignored) disambiguates the non-injective 'SymExpr' type
-- family.
hasWidth :: sym -> NatRepr w -> SymBV sym w -> SymBV sym w
hasWidth _ _ x = x

tests :: TestTree
tests = testGroup "What4.QQ"
  [ behaviorTests
  , snapshotTests
  ]

--------------------------------------------------------------------------------
-- Behavior

behaviorTests :: TestTree
behaviorTests = testGroup "behavior"
  [ testCase "bvadd of literals" $ withSym $ \sym -> do
      r <- [w4| add #b0011 #b0001 |] sym
      asBV (hasWidth sym (knownNat @4) r) @?= Just (BV.mkBV (knownNat @4) 4)

  , testCase "unparenthesized top-level application" $ withSym $ \sym -> do
      r <- [w4| add 2 3 |] sym
      asInteger r @?= Just 5

  , testCase "width-first bv literal" $ withSym $ \sym -> do
      r <- [w4| bv 8 42 |] sym
      asBV (hasWidth sym (knownNat @8) r) @?= Just (BV.mkBV (knownNat @8) 42)

  , testCase "bvadd with $ metavariable" $ withSym $ \sym -> do
      x <- bvLit sym (knownNat @8) (BV.mkBV (knownNat @8) 5)
      r <- [w4| add $x #b00000001 |] sym
      asBV (hasWidth sym (knownNat @8) r) @?= Just (BV.mkBV (knownNat @8) 6)

  , testCase "bv literal with @ width metavariable" $ withSym $ \sym -> do
      let w = knownNat @16
      r <- [w4| bv @w 42 |] sym
      asBV (hasWidth sym w r) @?= Just (BV.mkBV w 42)

  , testCase "integer addition" $ withSym $ \sym -> do
      r <- [w4| add 2 3 |] sym
      asInteger r @?= Just 5

  , testCase "decimal real literal is exact" $ withSym $ \sym -> do
      r <- [w4| 0.1 |] sym
      asRational r @?= Just (1 % 10)

  , testCase "negative decimal real literal is exact" $ withSym $ \sym -> do
      r <- [w4| -1.25 |] sym
      asRational r @?= Just ((-5) % 4)

  , testCase "integer n-ary addition" $ withSym $ \sym -> do
      r <- [w4| add 1 2 3 4 |] sym
      asInteger r @?= Just 10

  , testCase "subtraction" $ withSym $ \sym -> do
      r <- [w4| sub 10 3 |] sym
      asInteger r @?= Just 7

  , testCase "comparison and boolean structure" $ withSym $ \sym -> do
      p <- [w4| and (lt 1 2) (implies false true) |] sym
      asConstantPred p @?= Just True

  , testCase "equality" $ withSym $ \sym -> do
      p <- [w4| eq 1 1 |] sym
      asConstantPred p @?= Just True

  , testCase "if" $ withSym $ \sym -> do
      r <- [w4| if true 4 5 |] sym
      asInteger r @?= Just 4

  , testCase "zero_extend" $ withSym $ \sym -> do
      r <- [w4| zext 8 #b1010 |] sym
      asBV (hasWidth sym (knownNat @12) r) @?= Just (BV.mkBV (knownNat @12) 10)

  , testCase "sign_extend of negative" $ withSym $ \sym -> do
      r <- [w4| sext 4 #b1000 |] sym
      asBV (hasWidth sym (knownNat @8) r) @?= Just (BV.mkBV (knownNat @8) 0xF8)

  , testCase "extract" $ withSym $ \sym -> do
      r <- [w4| extract 3 0 #xAB |] sym
      asBV (hasWidth sym (knownNat @4) r) @?= Just (BV.mkBV (knownNat @4) 0xB)

  , testCase "concat" $ withSym $ \sym -> do
      r <- [w4| concat #b1010 #b0101 |] sym
      asBV (hasWidth sym (knownNat @8) r) @?= Just (BV.mkBV (knownNat @8) 0xA5)

  , testCase "bitwise and comparison ops" $ withSym $ \sym -> do
      p <- [w4| ult (and #xF0 #x0F) #xFF |] sym
      asConstantPred p @?= Just True

  , testCase "bitvector rotate" $ withSym $ \sym -> do
      r <- [w4| rol #b0001 (bv 4 1) |] sym
      asBV (hasWidth sym (knownNat @4) r) @?= Just (BV.mkBV (knownNat @4) 2)

  , testCase "generic equality and inequality" $ withSym $ \sym -> do
      p <- [w4| and (eq (bv 8 1) (bv 8 1)) (ne (bv 8 1) (bv 8 2)) |] sym
      asConstantPred p @?= Just True

  , testCase "let binding" $ withSym $ \sym -> do
      r <- [w4| let ((v (add 1 2))) (add v v) |] sym
      asInteger r @?= Just 6

  , testCase "hex literal value" $ withSym $ \sym -> do
      r <- [w4| #xFF |] sym
      asBV (hasWidth sym (knownNat @8) r) @?= Just (BV.mkBV (knownNat @8) 255)
  ]

--------------------------------------------------------------------------------
-- Generated-code snapshots
--
-- Each case pretty-prints the code 'w4' generates and compares it to a
-- golden file under test/golden/qq/. A diff shows exactly how codegen
-- changed; regenerate with @--accept@. Golden (rather than string
-- equality) because 'newName' counters may vary across GHC versions.

snapshotTests :: TestTree
snapshotTests = testGroup "snapshot"
  [ snap "bvadd-lits"   $(dumpW4 "add #b0011 #b0001")
  , snap "bvadd-meta"   $(dumpW4 "add $x #b00000001")
  , snap "plus"         $(dumpW4 "add 2 3")
  , snap "eq"           $(dumpW4 "eq 1 1")
  , snap "extract"      $(dumpW4 "extract 3 0 $x")
  , snap "let"          $(dumpW4 "let ((v (add 1 2))) (add v v)")
  , snap "if"           $(dumpW4 "if (lt 1 2) 3 4")
  , snap "zero-extend"  $(dumpW4 "zext 8 $x")
  ]
  where
    snap name code =
      goldenVsString name
        ("test/golden/qq/" ++ name ++ ".expected")
        (pure (BSL.pack (code ++ "\n")))
