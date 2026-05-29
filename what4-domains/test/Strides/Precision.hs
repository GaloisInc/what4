-- | Precision tests for strides operations.
--
-- Each lifted strides op should be at least as precise as the corresponding op
-- on the simple-hull projection of its inputs. The simple hull is the arc
-- @[start, start + n·stride]@: tight on non-self-wrapping orbits, and top on
-- self-wrapping ones (where @n·stride >= 2^w@). This is *not* what
-- 'S.toArith' returns — 'S.toArith' uses 'cosetArc' for self-wrap, which is
-- in general incomparable with strides results — but it /is/ the hull strides
-- can always claim to refine. We measure precision by /cardinality/:
--
-- @
-- S.size (S.op a b) <= A.size (A.op (hull a) (hull b))
-- @
--
-- Cardinality (rather than set inclusion) is the right comparison even with
-- this hull: a strides coset walk and the arith arc cover different elements
-- once strides has any nontrivial coset structure, so neither is uniformly a
-- subset of the other. A smaller cardinality is a tighter abstraction.
--
-- (Bitwise and rotation ops lift through 'B.Domain' rather than 'A.Domain',
-- so they are not compared against an Arith oracle here.)
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

-- | The arith hull of a strides progression: the arc
-- @[start, start + n·stride]@. Saturates to top when @n·stride >= 2^w@.
--
-- Differs from 'S.toArith', which falls back to 'cosetArc' on self-wrapping
-- orbits — that gives a tighter (but coset-shaped) hull that strides cannot
-- always refine.
hull :: (1 <= w) => NatRepr w -> S.Domain w -> A.Domain w
hull w c =
  A.interval (maxUnsigned w)
             (toInteger (S.start c))
             (toInteger (S.n c * S.stride c))

-- | The strides result has at most as many elements as the arith result.
sizeLeq ::
  (1 <= w, 1 <= u) =>
  NatRepr u -> S.Domain u -> A.Domain w -> Property
sizeLeq _w c arith =
  property (toInteger (S.size c) <= A.size arith)

-- | The strides result is contained in the arith result.
subsetOf ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> A.Domain w -> Natural -> Property
subsetOf _w c arith x =
  S.member c x ==> property (A.member arith (toInteger x))

precise_negate :: (1 <= w) => NatRepr w -> S.Domain w -> Property
precise_negate w c =
  S.proper c ==> sizeLeq w (S.negate w c) (A.negate (hull w c))

precise_add ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_add w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.add w a b) (A.add (hull w a) (hull w b))

precise_sub ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_sub w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.sub w a b) (A.add (hull w a) (A.negate (hull w b)))

precise_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> S.Domain w -> Property
precise_scale w k c =
  S.proper c ==> sizeLeq w (S.scale w k c) (A.scale k (hull w c))

-- Note: there is no @precise_mul@ (or @subset_mul@). Closed-form @mul@'s
-- cross-term @i·j·t1·t2@ walks the coset of @start'@ out of order, so
-- @n'@ overcounts when the walk revisits residues. The result is a coset
-- progression that is incomparable in cardinality (and as a set) with the
-- arith arc, even when both operands fit @[start, start + n·stride]@. The
-- principled fix is a reduced product Strides x Arith, which is future work.

precise_udiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_udiv w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.udiv w a b) (A.udiv (hull w a) (hull w b))

precise_urem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_urem w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.urem w a b) (A.urem (hull w a) (hull w b))

precise_sdiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_sdiv w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.sdiv w a b) (A.sdiv w (hull w a) (hull w b))

precise_srem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_srem w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.srem w a b) (A.srem w (hull w a) (hull w b))

precise_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_udivSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.udivSmtlib w a b) (A.udivSmtlib (hull w a) (hull w b))

precise_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_uremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.uremSmtlib w a b) (A.uremSmtlib (hull w a) (hull w b))

precise_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_sdivSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.sdivSmtlib w a b) (A.sdivSmtlib w (hull w a) (hull w b))

precise_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_sremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.sremSmtlib w a b) (A.sremSmtlib w (hull w a) (hull w b))

precise_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
precise_zext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> sizeLeq u (S.zext w c u) (A.zext (hull w c) u)

precise_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
precise_sext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> sizeLeq u (S.sext w c u) (A.sext w (hull w c) u)

precise_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> S.Domain u -> NatRepr v -> S.Domain v -> Property
precise_concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      S.proper a ==> S.proper b ==>
        sizeLeq (NR.addNat u v) (S.concat u a v b)
                (A.concat u (hull u a) v (hull v b))

precise_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> S.Domain w -> Property
precise_select i n w c =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      S.proper c ==> sizeLeq n (S.select i n w c) (A.select i n (hull w c))

precise_shl ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_shl w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.shl w a b) (A.shl w (hull w a) (hull w b))

precise_lshr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_lshr w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.lshr w a b) (A.lshr w (hull w a) (hull w b))

precise_ashr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_ashr w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.ashr w a b) (A.ashr w (hull w a) (hull w b))

-- ------------------------------------------------------------------
-- * Subset properties
--
-- Each strides result is /also/ a subset of the corresponding arith result
-- (when this holds — closed-form @mul@, for instance, walks a coset that
-- can leave the arith convex hull). We test it everywhere and let the
-- failures tell us which ops actually do.

subset_negate :: (1 <= w) => NatRepr w -> S.Domain w -> Natural -> Property
subset_negate w c x =
  S.proper c ==> subsetOf w (S.negate w c) (A.negate (S.toArith c)) x

subset_add ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_add w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.add w a b) (A.add (S.toArith a) (S.toArith b)) x

subset_sub ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_sub w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.sub w a b) (A.add (S.toArith a) (A.negate (S.toArith b))) x

subset_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> S.Domain w -> Natural -> Property
subset_scale w k c x =
  S.proper c ==> subsetOf w (S.scale w k c) (A.scale k (S.toArith c)) x

subset_udiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_udiv w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.udiv w a b) (A.udiv (S.toArith a) (S.toArith b)) x

subset_urem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_urem w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.urem w a b) (A.urem (S.toArith a) (S.toArith b)) x

subset_sdiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_sdiv w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.sdiv w a b) (A.sdiv w (S.toArith a) (S.toArith b)) x

subset_srem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_srem w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.srem w a b) (A.srem w (S.toArith a) (S.toArith b)) x

subset_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_udivSmtlib w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.udivSmtlib w a b) (A.udivSmtlib (S.toArith a) (S.toArith b)) x

subset_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_uremSmtlib w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.uremSmtlib w a b) (A.uremSmtlib (S.toArith a) (S.toArith b)) x

subset_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_sdivSmtlib w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.sdivSmtlib w a b) (A.sdivSmtlib w (S.toArith a) (S.toArith b)) x

subset_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_sremSmtlib w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.sremSmtlib w a b) (A.sremSmtlib w (S.toArith a) (S.toArith b)) x

subset_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Natural -> Property
subset_zext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> subsetOf u (S.zext w c u) (A.zext (S.toArith c) u) x

subset_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Natural -> Property
subset_sext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> subsetOf u (S.sext w c u) (A.sext w (S.toArith c) u) x

subset_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> S.Domain u -> NatRepr v -> S.Domain v -> Natural -> Property
subset_concat u a v b x =
  case NR.leqAddPos u v of
    LeqProof ->
      S.proper a ==> S.proper b ==>
        subsetOf (NR.addNat u v) (S.concat u a v b)
                 (A.concat u (S.toArith a) v (S.toArith b)) x

subset_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> S.Domain w -> Natural -> Property
subset_select i n w c x =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      S.proper c ==> subsetOf n (S.select i n w c) (A.select i n (S.toArith c)) x

subset_shl ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_shl w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.shl w a b) (A.shl w (S.toArith a) (S.toArith b)) x

subset_lshr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_lshr w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.lshr w a b) (A.lshr w (S.toArith a) (S.toArith b)) x

subset_ashr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Natural -> Property
subset_ashr w a b x =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.ashr w a b) (A.ashr w (S.toArith a) (S.toArith b)) x

tests :: TT.TestTree
tests = TT.testGroup "Precision (Strides at least as precise as Arith)"
  [ genTest "precise_negate" $
      do SW n <- genWidth
         precise_negate n <$> S.genDomain n
  , genTest "precise_add" $
      do SW n <- genWidth
         precise_add n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_sub" $
      do SW n <- genWidth
         precise_sub n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_scale" $
      do SW n <- genWidth
         precise_scale n <$> chooseInteger (0, maxUnsigned n)
                         <*> S.genDomain n
  , genTest "precise_udiv" $
      do SW n <- genWidth
         precise_udiv n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_urem" $
      do SW n <- genWidth
         precise_urem n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_sdiv" $
      do SW n <- genWidth
         precise_sdiv n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_srem" $
      do SW n <- genWidth
         precise_srem n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_udivSmtlib" $
      do SW n <- genWidth
         precise_udivSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_uremSmtlib" $
      do SW n <- genWidth
         precise_uremSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_sdivSmtlib" $
      do SW n <- genWidth
         precise_sdivSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_sremSmtlib" $
      do SW n <- genWidth
         precise_sremSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                pure (precise_zext w c u)
  , genTest "precise_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                pure (precise_sext w c u)
  , genTest "precise_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- S.genDomain m
         b <- S.genDomain n
         pure (precise_concat m a n b)
  , genTest "precise_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- S.genDomain w
         pure (precise_select i n w c)
  , genTest "precise_shl" $
      do SW n <- genWidth
         precise_shl n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_lshr" $
      do SW n <- genWidth
         precise_lshr n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_ashr" $
      do SW n <- genWidth
         precise_ashr n <$> S.genDomain n <*> S.genDomain n

  -- Subset properties (a strides result is also a subset of arith).
  -- Some of these are expected to fail for ops whose closed form walks
  -- a coset that leaves the arith convex hull (e.g., 'mul').
  , genTest "subset_negate" $
      do SW n <- genWidth
         subset_negate n <$> S.genDomain n <*> genNatBV n
  , genTest "subset_add" $
      do SW n <- genWidth
         subset_add n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_sub" $
      do SW n <- genWidth
         subset_sub n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_scale" $
      do SW n <- genWidth
         subset_scale n <$> chooseInteger (0, maxUnsigned n)
                        <*> S.genDomain n <*> genNatBV n
  , genTest "subset_udiv" $
      do SW n <- genWidth
         subset_udiv n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_urem" $
      do SW n <- genWidth
         subset_urem n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_sdiv" $
      do SW n <- genWidth
         subset_sdiv n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_srem" $
      do SW n <- genWidth
         subset_srem n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_udivSmtlib" $
      do SW n <- genWidth
         subset_udivSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_uremSmtlib" $
      do SW n <- genWidth
         subset_uremSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_sdivSmtlib" $
      do SW n <- genWidth
         subset_sdivSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_sremSmtlib" $
      do SW n <- genWidth
         subset_sremSmtlib n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV u
                pure (subset_zext w c u x)
  , genTest "subset_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV u
                pure (subset_sext w c u x)
  , genTest "subset_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- S.genDomain m
         b <- S.genDomain n
         x <- genNatBV (addNat m n)
         pure (subset_concat m a n b x)
  , genTest "subset_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- S.genDomain w
         x <- genNatBV n
         pure (subset_select i n w c x)
  , genTest "subset_shl" $
      do SW n <- genWidth
         subset_shl n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_lshr" $
      do SW n <- genWidth
         subset_lshr n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "subset_ashr" $
      do SW n <- genWidth
         subset_ashr n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  ]
