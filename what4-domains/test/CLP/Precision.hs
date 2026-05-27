-- | Precision tests for CLP operations.
--
-- Each lifted CLP op should be at least as precise as the corresponding op
-- on the @toArith@ projections of its inputs. The general form is:
--
-- @
-- C.member (op a b) x ==> A.member (A.op (C.toArith a) (C.toArith b)) x
-- @
--
-- i.e. every concrete value the CLP result claims as a member is also in the
-- Arith result on the projections, so the CLP result is contained in the
-- Arith result. (Bitwise and rotation ops lift through 'B.Domain' rather
-- than 'A.Domain', so they are not compared against an Arith oracle here.)
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module CLP.Precision (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (+), type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.CLP as C
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

precise_negate :: (1 <= w) => NatRepr w -> C.Clp w -> Natural -> Property
precise_negate w c x =
  C.proper c ==> C.member (C.negate w c) x ==>
    property (A.member (A.negate (C.toArith c)) (toInteger x))

precise_add ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_add w a b x =
  C.proper a ==> C.proper b ==> C.member (C.add w a b) x ==>
    property (A.member (A.add (C.toArith a) (C.toArith b)) (toInteger x))

precise_sub ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_sub w a b x =
  C.proper a ==> C.proper b ==> C.member (C.sub w a b) x ==>
    property (A.member (A.add (C.toArith a) (A.negate (C.toArith b))) (toInteger x))

precise_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> C.Clp w -> Natural -> Property
precise_scale w k c x =
  C.proper c ==> C.member (C.scale w k c) x ==>
    property (A.member (A.scale k (C.toArith c)) (toInteger x))

precise_mul ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_mul w a b x =
  C.proper a ==> C.proper b ==> C.member (C.mul w a b) x ==>
    property (A.member (A.mul (C.toArith a) (C.toArith b)) (toInteger x))

precise_udiv ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_udiv w a b x =
  C.proper a ==> C.proper b ==> C.member (C.udiv w a b) x ==>
    property (A.member (A.udiv (C.toArith a) (C.toArith b)) (toInteger x))

precise_urem ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_urem w a b x =
  C.proper a ==> C.proper b ==> C.member (C.urem w a b) x ==>
    property (A.member (A.urem (C.toArith a) (C.toArith b)) (toInteger x))

precise_sdiv ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_sdiv w a b x =
  C.proper a ==> C.proper b ==> C.member (C.sdiv w a b) x ==>
    property (A.member (A.sdiv w (C.toArith a) (C.toArith b)) (toInteger x))

precise_srem ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_srem w a b x =
  C.proper a ==> C.proper b ==> C.member (C.srem w a b) x ==>
    property (A.member (A.srem w (C.toArith a) (C.toArith b)) (toInteger x))

precise_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_udivSmtlib w a b x =
  C.proper a ==> C.proper b ==> C.member (C.udivSmtlib w a b) x ==>
    property (A.member (A.udivSmtlib (C.toArith a) (C.toArith b)) (toInteger x))

precise_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_uremSmtlib w a b x =
  C.proper a ==> C.proper b ==> C.member (C.uremSmtlib w a b) x ==>
    property (A.member (A.uremSmtlib (C.toArith a) (C.toArith b)) (toInteger x))

precise_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_sdivSmtlib w a b x =
  C.proper a ==> C.proper b ==> C.member (C.sdivSmtlib w a b) x ==>
    property (A.member (A.sdivSmtlib w (C.toArith a) (C.toArith b)) (toInteger x))

precise_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_sremSmtlib w a b x =
  C.proper a ==> C.proper b ==> C.member (C.sremSmtlib w a b) x ==>
    property (A.member (A.sremSmtlib w (C.toArith a) (C.toArith b)) (toInteger x))

precise_zext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> C.Clp w -> NatRepr u -> Natural -> Property
precise_zext w c u x =
  C.proper c ==> C.member (C.zext w c u) x ==>
    property (A.member (A.zext (C.toArith c) u) (toInteger x))

precise_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> C.Clp w -> NatRepr u -> Natural -> Property
precise_sext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      C.proper c ==> C.member (C.sext w c u) x ==>
        property (A.member (A.sext w (C.toArith c) u) (toInteger x))

precise_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> C.Clp u -> NatRepr v -> C.Clp v -> Natural -> Property
precise_concat u a v b x =
  case NR.leqAddPos u v of
    LeqProof ->
      C.proper a ==> C.proper b ==> C.member (C.concat u a v b) x ==>
        property (A.member (A.concat u (C.toArith a) v (C.toArith b)) (toInteger x))

precise_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> C.Clp w -> Natural -> Property
precise_select i n w c x =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      C.proper c ==> C.member (C.select i n w c) x ==>
        property (A.member (A.select i n (C.toArith c)) (toInteger x))

precise_shl ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_shl w a b x =
  C.proper a ==> C.proper b ==> C.member (C.shl w a b) x ==>
    property (A.member (A.shl w (C.toArith a) (C.toArith b)) (toInteger x))

precise_lshr ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_lshr w a b x =
  C.proper a ==> C.proper b ==> C.member (C.lshr w a b) x ==>
    property (A.member (A.lshr w (C.toArith a) (C.toArith b)) (toInteger x))

precise_ashr ::
  (1 <= w) =>
  NatRepr w -> C.Clp w -> C.Clp w -> Natural -> Property
precise_ashr w a b x =
  C.proper a ==> C.proper b ==> C.member (C.ashr w a b) x ==>
    property (A.member (A.ashr w (C.toArith a) (C.toArith b)) (toInteger x))

tests :: TT.TestTree
tests = TT.testGroup "Precision (CLP at least as precise as Arith)"
  [ genTest "precise_negate" $
      do SW n <- genWidth
         precise_negate n <$> C.genClp n <*> genNatBV n
  , genTest "precise_add" $
      do SW n <- genWidth
         precise_add n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_sub" $
      do SW n <- genWidth
         precise_sub n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_scale" $
      do SW n <- genWidth
         precise_scale n <$> chooseInteger (0, maxUnsigned n)
                         <*> C.genClp n <*> genNatBV n
  , genTest "precise_mul" $
      do SW n <- genWidth
         precise_mul n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_udiv" $
      do SW n <- genWidth
         precise_udiv n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_urem" $
      do SW n <- genWidth
         precise_urem n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_sdiv" $
      do SW n <- genWidth
         precise_sdiv n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_srem" $
      do SW n <- genWidth
         precise_srem n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_udivSmtlib" $
      do SW n <- genWidth
         precise_udivSmtlib n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_uremSmtlib" $
      do SW n <- genWidth
         precise_uremSmtlib n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_sdivSmtlib" $
      do SW n <- genWidth
         precise_sdivSmtlib n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_sremSmtlib" $
      do SW n <- genWidth
         precise_sremSmtlib n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- C.genClp w
                x <- genNatBV u
                pure (precise_zext w c u x)
  , genTest "precise_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- C.genClp w
                x <- genNatBV u
                pure (precise_sext w c u x)
  , genTest "precise_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- C.genClp m
         b <- C.genClp n
         x <- genNatBV (addNat m n)
         pure (precise_concat m a n b x)
  , genTest "precise_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- C.genClp w
         x <- genNatBV n
         pure (precise_select i n w c x)
  , genTest "precise_shl" $
      do SW n <- genWidth
         precise_shl n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_lshr" $
      do SW n <- genWidth
         precise_lshr n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  , genTest "precise_ashr" $
      do SW n <- genWidth
         precise_ashr n <$> C.genClp n <*> C.genClp n <*> genNatBV n
  ]
