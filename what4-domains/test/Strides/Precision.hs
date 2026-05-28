-- | Precision tests for strides operations.
--
-- Each lifted strides op should be at least as precise as the corresponding op
-- on the @toArith@ projections of its inputs. The general form is:
--
-- @
-- S.member (op a b) x ==> A.member (A.op (S.toArith a) (S.toArith b)) x
-- @
--
-- i.e. every concrete value the strides result claims as a member is also in
-- the Arith result on the projections, so the strides result is contained in
-- the Arith result. (Bitwise and rotation ops lift through 'B.Domain' rather
-- than 'A.Domain', so they are not compared against an Arith oracle here.)
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Strides.Precision (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (+), type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Strides as S
import           What4.Domains.Verification (Gen, Property, chooseInt, chooseInteger, getSize, property, (==>))
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

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

precise_negate :: (1 <= w) => NatRepr w -> S.Domain w -> Natural -> Property
precise_negate w c x =
  S.proper c ==> S.member (S.negate w c) x ==>
    property (A.member (A.negate (S.toArith c)) (toInteger x))

precise_add ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_add w a b x =
  S.proper a ==> S.proper b ==> S.member (S.add w a b) x ==>
    property (A.member (A.add (S.toArith a) (S.toArith b)) (toInteger x))

precise_sub ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_sub w a b x =
  S.proper a ==> S.proper b ==> S.member (S.sub w a b) x ==>
    property (A.member (A.add (S.toArith a) (A.negate (S.toArith b))) (toInteger x))

precise_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> S.Domain w -> Natural -> Property
precise_scale w k c x =
  S.proper c ==> S.member (S.scale w k c) x ==>
    property (A.member (A.scale k (S.toArith c)) (toInteger x))

precise_mul ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_mul w a b x =
  S.proper a ==> S.proper b ==> S.member (S.mul w a b) x ==>
    property (A.member (A.mul (S.toArith a) (S.toArith b)) (toInteger x))

precise_udiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_udiv w a b x =
  S.proper a ==> S.proper b ==> S.member (S.udiv w a b) x ==>
    property (A.member (A.udiv (S.toArith a) (S.toArith b)) (toInteger x))

precise_urem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_urem w a b x =
  S.proper a ==> S.proper b ==> S.member (S.urem w a b) x ==>
    property (A.member (A.urem (S.toArith a) (S.toArith b)) (toInteger x))

precise_sdiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_sdiv w a b x =
  S.proper a ==> S.proper b ==> S.member (S.sdiv w a b) x ==>
    property (A.member (A.sdiv w (S.toArith a) (S.toArith b)) (toInteger x))

precise_srem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_srem w a b x =
  S.proper a ==> S.proper b ==> S.member (S.srem w a b) x ==>
    property (A.member (A.srem w (S.toArith a) (S.toArith b)) (toInteger x))

precise_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_udivSmtlib w a b x =
  S.proper a ==> S.proper b ==> S.member (S.udivSmtlib w a b) x ==>
    property (A.member (A.udivSmtlib (S.toArith a) (S.toArith b)) (toInteger x))

precise_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_uremSmtlib w a b x =
  S.proper a ==> S.proper b ==> S.member (S.uremSmtlib w a b) x ==>
    property (A.member (A.uremSmtlib (S.toArith a) (S.toArith b)) (toInteger x))

precise_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_sdivSmtlib w a b x =
  S.proper a ==> S.proper b ==> S.member (S.sdivSmtlib w a b) x ==>
    property (A.member (A.sdivSmtlib w (S.toArith a) (S.toArith b)) (toInteger x))

precise_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_sremSmtlib w a b x =
  S.proper a ==> S.proper b ==> S.member (S.sremSmtlib w a b) x ==>
    property (A.member (A.sremSmtlib w (S.toArith a) (S.toArith b)) (toInteger x))

precise_zext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Natural -> Property
precise_zext w c u x =
  S.proper c ==> S.member (S.zext w c u) x ==>
    property (A.member (A.zext (S.toArith c) u) (toInteger x))

precise_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Natural -> Property
precise_sext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> S.member (S.sext w c u) x ==>
        property (A.member (A.sext w (S.toArith c) u) (toInteger x))

precise_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> S.Domain u -> NatRepr v -> S.Domain v -> Natural -> Property
precise_concat u a v b x =
  case NR.leqAddPos u v of
    LeqProof ->
      S.proper a ==> S.proper b ==> S.member (S.concat u a v b) x ==>
        property (A.member (A.concat u (S.toArith a) v (S.toArith b)) (toInteger x))

precise_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> S.Domain w -> Natural -> Property
precise_select i n w c x =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      S.proper c ==> S.member (S.select i n w c) x ==>
        property (A.member (A.select i n (S.toArith c)) (toInteger x))

precise_shl ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_shl w a b x =
  S.proper a ==> S.proper b ==> S.member (S.shl w a b) x ==>
    property (A.member (A.shl w (S.toArith a) (S.toArith b)) (toInteger x))

precise_lshr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_lshr w a b x =
  S.proper a ==> S.proper b ==> S.member (S.lshr w a b) x ==>
    property (A.member (A.lshr w (S.toArith a) (S.toArith b)) (toInteger x))

precise_ashr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
precise_ashr w a b x =
  S.proper a ==> S.proper b ==> S.member (S.ashr w a b) x ==>
    property (A.member (A.ashr w (S.toArith a) (S.toArith b)) (toInteger x))

tests :: TT.TestTree
tests = TT.testGroup "Precision (Strides at least as precise as Arith)"
  [ genTest "precise_negate" $
      do SW n <- genWidth
         precise_negate n <$> S.genDomain n <*> genNatBV n
  , genTest "precise_add" $
      do SW n <- genWidth
         precise_add n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_sub" $
      do SW n <- genWidth
         precise_sub n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_scale" $
      do SW n <- genWidth
         precise_scale n <$> chooseInteger (0, maxUnsigned n)
                         <*> S.genDomain n <*> genNatBV n
  , genTest "precise_mul" $
      do SW n <- genWidth
         precise_mul n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_udiv" $
      do SW n <- genWidth
         precise_udiv n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_urem" $
      do SW n <- genWidth
         precise_urem n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_sdiv" $
      do SW n <- genWidth
         precise_sdiv n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_srem" $
      do SW n <- genWidth
         precise_srem n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_udivSmtlib" $
      do SW n <- genWidth
         precise_udivSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_uremSmtlib" $
      do SW n <- genWidth
         precise_uremSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_sdivSmtlib" $
      do SW n <- genWidth
         precise_sdivSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_sremSmtlib" $
      do SW n <- genWidth
         precise_sremSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV u
                pure (precise_zext w c u x)
  , genTest "precise_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV u
                pure (precise_sext w c u x)
  , genTest "precise_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- S.genDomain m
         b <- S.genDomain n
         x <- genNatBV (addNat m n)
         pure (precise_concat m a n b x)
  , genTest "precise_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- S.genDomain w
         x <- genNatBV n
         pure (precise_select i n w c x)
  , genTest "precise_shl" $
      do SW n <- genWidth
         precise_shl n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_lshr" $
      do SW n <- genWidth
         precise_lshr n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "precise_ashr" $
      do SW n <- genWidth
         precise_ashr n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  ]
