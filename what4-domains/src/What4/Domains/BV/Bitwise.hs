{-|
Module      : What4.Domains.BV.Bitwise
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : huffman@galois.com

Provides a bitwise implementation of bitvector abstract domains.
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.Bitwise
  ( Domain(..)
  , bitle
  , proper
  , bvdMask
  , member
  , pmember
  , size
  , asSingleton
  , nonempty
  , eq
  , slt
  , ult
  , domainsOverlap
  , bitbounds
  , ubounds
  , sbounds
  -- * Lattice operations
  , top
  , any
  , bottom
  , isBottom
  , join
  , union
  , meet
  , intersection
  , leq
  -- * Operations
  , singleton
  , range
  , interval
  , concat
  , select
  , zext
  , sext
  , testBit
  -- ** shifts and rotates
  , shl
  , lshr
  , ashr
  , rol
  , ror
  , shlAbstract
  , lshrAbstract
  , ashrAbstract
  , rolAbstract
  , rorAbstract
  , shlAbstractSpec
  , lshrAbstractSpec
  , ashrAbstractSpec
  , rolAbstractSpec
  , rorAbstractSpec
  -- ** arithmetic
  , add
  , sub
  , negate
  , scale
  , mul
  , mulPrecise
  , udiv
  , urem
  , sdiv
  , srem
  , udivPrecise
  , uremPrecise
  -- ** arithmetic (SMT-LIB div-by-zero semantics)
  , udivSmtlib
  , uremSmtlib
  , sdivSmtlib
  , sremSmtlib
  -- ** bitwise logical
  , and
  , or
  , xor
  , not

  -- * Correctness properties
  , genDomain
  , genElement
  , genPair
  , correct_any
  , correct_singleton
  , correct_overlap
  , correct_overlap_inv
  , correct_asSingleton
  , correct_union
  , correct_intersection
  , correct_join
  , correct_meet
  , precise_meet
  , correct_leq
  -- ** Lattice laws
  , join_commutative
  , join_idempotent
  , meet_commutative
  , meet_idempotent
  , join_top
  , join_bottom
  , meet_top
  , meet_bottom
  , leq_reflexive
  , join_upper_bound
  , join_proper
  , meet_proper
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_shrink
  , correct_trunc
  , correct_select
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
  , correct_shlAbstract
  , correct_lshrAbstract
  , correct_ashrAbstract
  , correct_rolAbstract
  , correct_rorAbstract
  , correct_equiv_shlAbstract
  , correct_equiv_lshrAbstract
  , correct_equiv_ashrAbstract
  , correct_equiv_rolAbstract
  , correct_equiv_rorAbstract
  , correct_eq
  , correct_ult
  , correct_slt
  , correct_ubounds
  , correct_sbounds
  , correct_add
  , correct_sub
  , correct_neg
  , correct_scale
  , correct_mul
  , correct_mulPrecise
  , correct_udiv
  , correct_urem
  , correct_sdiv
  , correct_srem
  , correct_udivPrecise
  , correct_uremPrecise
  , correct_udivSmtlib
  , correct_uremSmtlib
  , correct_sdivSmtlib
  , correct_sremSmtlib
  , correct_and
  , correct_or
  , correct_not
  , correct_xor
  , correct_testBit
  ) where

import           Data.Bits hiding (testBit, xor)
import qualified Data.Bits as Bits
import           Data.Parameterized.NatRepr
import           Numeric.Natural
import           GHC.TypeNats
import           What4.Domains.BV.Bitwise.Tnum (Tnum)
import qualified What4.Domains.BV.Bitwise.Tnum as Tnum
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInteger)

import qualified Prelude
import           Prelude hiding (any, concat, negate, and, or, not)

import qualified What4.Domains.Arithmetic as Arith

-- | A bitwise interval domain, defined via a
--   bitwise upper and lower bound.  The ordering
--   used here to construct the interval is the pointwise
--   ordering on bits.  In particular @x [= y iff x .|. y == y@,
--   and a value @x@ is in the set defined by the pair @(lo,hi)@
--   just when @lo [= x && x [= hi@.
data Domain (w :: Nat) =
  BVBitInterval !Integer !Integer !Integer
  -- ^ @BVDBitInterval mask lo hi@.
  --  @mask@ caches the value of @2^w - 1@
  deriving (Eq, Ord, Show)

-- | /O(w)/. Test if the domain satisfies its invariants.
proper :: NatRepr w -> Domain w -> Bool
proper w (BVBitInterval mask lo hi) =
  mask == maxUnsigned w &&
  bitle lo mask &&
  bitle hi mask &&
  bitle lo hi

-- | /O(w)/. Test if the given integer value is a member of the abstract domain.
member :: Domain w -> Integer -> Bool
member (BVBitInterval mask lo hi) x = bitle lo x' && bitle x' hi
  where x' = x .&. mask

-- | /O(w)/. Compute how many concrete elements are in the abstract domain.
size :: Domain w -> Integer
size d@(BVBitInterval _ lo hi)
  | bitle lo hi = Bits.bit (Bits.popCount (unknownBits d))
  | otherwise   = 0

bitle :: Integer -> Integer -> Bool
bitle x y = (x .|. y) == y

-- | /O(1)/. The set of bit positions whose values are not constant
-- throughout the domain — i.e.\ the tristate-number mask. Bits set here
-- vary; bits clear here are determined (and equal in @lo@ and @hi@).
unknownBits :: Domain w -> Integer
unknownBits (BVBitInterval _ lo hi) = lo `Bits.xor` hi
{-# INLINE unknownBits #-}

-- | /O(1)/. Return the bitvector mask value from this domain.
bvdMask :: Domain w -> Integer
bvdMask (BVBitInterval mask _ _) = mask

-- | Random generator for domain values.  We always generate
--   nonempty domain values.
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w =
  do let mask = maxUnsigned w
     lo <- chooseInteger (0, mask)
     hi <- chooseInteger (0, mask)
     pure $! interval mask lo (lo .|. hi)

-- This generator goes to some pains to try
-- to generate a good statistical distribution
-- of the values in the domain.  It only chooses
-- random bits for the "unknown" values of
-- the domain, then stripes them out among
-- the unknown bit positions.
genElement :: Domain w -> Gen Integer
genElement d@(BVBitInterval _mask lo _) =
  do x <- chooseInteger (0, bit bs - 1)
     pure $ stripe lo x 0

 where
 u = unknownBits d
 bs = Bits.popCount u
 stripe val x i
   | x == 0 = val
   | Bits.testBit u i =
       let val' = if Bits.testBit x 0 then setBit val i else val in
       stripe val' (x `shiftR` 1) (i + 1)
   | otherwise = stripe val x (i + 1)

{- A faster generator, but I worry that it
   doesn't have very good statistical properties...

genElement :: Domain w -> Gen Integer
genElement (BVBitInterval mask lo hi) =
  do let u = Bits.xor lo hi
     x <- chooseInteger (0, mask)
     pure ((x .&. u) .|. lo)
-}

-- | Generate a random nonempty domain and an element
--   contained in that domain.
genPair :: NatRepr w -> Gen (Domain w, Integer)
genPair w =
  do a <- genDomain w
     x <- genElement a
     return (a,x)

-- | /O(1)/. Unsafe constructor for internal use.
interval :: Integer -> Integer -> Integer -> Domain w
interval mask lo hi = BVBitInterval mask lo hi

-- | /O(w)/. Construct a domain from bitwise lower and upper bounds.
range :: NatRepr w -> Integer -> Integer -> Domain w
range w lo hi = BVBitInterval (maxUnsigned w) lo' hi'
  where
  lo'  = lo .&. mask
  hi'  = hi .&. mask
  mask = maxUnsigned w

-- | /O(1)/. Bitwise lower and upper bounds.
bitbounds :: Domain w -> (Integer, Integer)
bitbounds (BVBitInterval _ lo hi) = (lo, hi)

-- | /O(w)/. Test if this domain contains a single value, and return it if so.
asSingleton :: Domain w -> Maybe Integer
asSingleton (BVBitInterval _ lo hi) = if lo == hi then Just lo else Nothing

-- | /O(w)/. Returns true iff there is at least one element
-- in this bitwise domain.
nonempty :: Domain w -> Bool
nonempty (BVBitInterval _mask lo hi) = bitle lo hi

------------------------------------------------------------------------
-- Lattice operations

-- | /O(1)/. Top element of the lattice: represents all bitvectors of width @w@.
top :: NatRepr w -> Domain w
top w = BVBitInterval mask 0 mask
  where
  mask = maxUnsigned w
{-# INLINE top #-}

-- | /O(w)/. Bitwise domain containing every bitvector value.
{-# DEPRECATED any "Use 'top' instead" #-}
any :: NatRepr w -> Domain w
any = top
{-# INLINE any #-}

-- | /O(1)/. Bottom element of the lattice: represents the empty set of bitvectors.
-- This is an improper domain whose membership predicate is unsatisfiable.
bottom :: NatRepr w -> Domain w
bottom w = BVBitInterval mask mask 0
  where
  mask = maxUnsigned w
{-# INLINE bottom #-}

-- | /O(1)/.
isBottom :: Domain w -> Bool
isBottom (BVBitInterval mask lo hi) = lo == mask && hi == 0

-- | /O(w)/. Lattice join: pointwise least upper bound on the bit-level @bitle@ ordering.
join :: Domain w -> Domain w -> Domain w
join (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .&. blo) (ahi .|. bhi)

{-# DEPRECATED union "Use 'join' instead" #-}
union :: Domain w -> Domain w -> Domain w
union = join
{-# INLINE union #-}

-- | /O(w)/. Lattice meet: pointwise greatest lower bound on the bit-level @bitle@ ordering.
-- If both inputs are proper (or bottom), so is the result.
meet :: Domain w -> Domain w -> Domain w
meet (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi)
  | bitle lo hi = BVBitInterval mask lo hi
  | otherwise   = BVBitInterval mask mask 0  -- canonical bottom
  where
    lo = alo .|. blo
    hi = ahi .&. bhi

{-# DEPRECATED intersection "Use 'meet' instead" #-}
intersection :: Domain w -> Domain w -> Domain w
intersection = meet
{-# INLINE intersection #-}

-- | /O(w)/. Lattice ordering: @leq a b@ returns 'True' if every concrete value
-- represented by @a@ is also represented by @b@.
leq :: Domain w -> Domain w -> Bool
leq (BVBitInterval _ alo ahi) (BVBitInterval _ blo bhi) =
  bitle blo alo && bitle ahi bhi
{-# INLINE leq #-}

------------------------------------------------------------------------
-- Operations

-- | /O(w)/. Return a domain containing just the given value.
singleton :: NatRepr w -> Integer -> Domain w
singleton w x = BVBitInterval mask x' x'
  where
  x' = x .&. mask
  mask = maxUnsigned w

-- | /O(w)/. Returns true iff the domains have some value in common.
domainsOverlap :: Domain w -> Domain w -> Bool
domainsOverlap a b = nonempty (meet a b)

-- | /O(w)/. Decide equality of two domains: 'Just True' if both are the same
-- singleton, 'Just False' if they're disjoint, 'Nothing' otherwise.
eq :: Domain w -> Domain w -> Maybe Bool
eq a b
  | Just x <- asSingleton a
  , Just y <- asSingleton b
  = Just (x == y)

  | Prelude.not (domainsOverlap a b) = Just False
  | otherwise = Nothing

-- | /O(u + v)/. @concat a y@ returns a domain where each element in @a@ has
-- been concatenated with an element in @y@. The most-significant bits are
-- @a@, and the least significant bits are @y@.
concat :: NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u (BVBitInterval _ alo ahi) v (BVBitInterval _ blo bhi) =
    BVBitInterval mask (cat alo blo) (cat ahi bhi)
  where
    cat i j = (i `shiftL` widthVal v) + j
    mask = maxUnsigned (addNat u v)

-- | /O(w)/. @shrink i a@ drops the @i@ least significant bits from @a@.
shrink ::
  NatRepr i ->
  Domain (i + n) -> Domain n
shrink i (BVBitInterval mask lo hi) = BVBitInterval (shr mask) (shr lo) (shr hi)
  where
  shr x = x `shiftR` widthVal i

-- | /O(w)/. @trunc n d@ selects the @n@ least significant bits from @d@.
trunc ::
  (n <= w) =>
  NatRepr n ->
  Domain w ->
  Domain n
trunc n (BVBitInterval _ lo hi) = range n lo hi

-- | /O(w)/. @select i n a@ selects @n@ bits starting from index @i@ from @a@.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  Domain w -> Domain n
select i n a = shrink i (trunc (addNat i n) a)

-- | /O(w)/. Zero-extend a domain to a larger width.
zext :: (1 <= w, w + 1 <= u) => Domain w -> NatRepr u -> Domain u
zext (BVBitInterval _ lo hi) u = range u lo hi

-- | /O(w)/. Sign-extend a domain to a larger width.
sext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w (BVBitInterval _ lo hi) u = range u lo' hi'
  where
  lo' = toSigned w lo
  hi' = toSigned w hi

-- | /O(w)/. Test bit @i@ of every value in the domain: 'Just True' if it is
-- set in every member, 'Just False' if clear in every member, 'Nothing' if
-- it varies.
testBit :: Domain w -> Natural -> Maybe Bool
testBit (BVBitInterval _mask lo hi) i = if lob == hib then Just lob else Nothing
  where
  lob = Bits.testBit lo j
  hib = Bits.testBit hi j
  j = fromIntegral i

-- | /O(w)/. Shift left by a known amount.
shl :: NatRepr w -> Domain w -> Integer -> Domain w
shl w (BVBitInterval mask lo hi) y = BVBitInterval mask (shleft lo) (shleft hi)
  where
  y' = fromInteger (min y (intValue w))
  shleft x = (x `shiftL` y') .&. mask

-- | /O(w)/. Rotate left by a known amount.
rol :: NatRepr w -> Domain w -> Integer -> Domain w
rol w (BVBitInterval mask lo hi) y =
  BVBitInterval mask (Arith.rotateLeft w lo y) (Arith.rotateLeft w hi y)

-- | /O(w)/. Rotate right by a known amount.
ror :: NatRepr w -> Domain w -> Integer -> Domain w
ror w (BVBitInterval mask lo hi) y =
  BVBitInterval mask (Arith.rotateRight w lo y) (Arith.rotateRight w hi y)

-- | /O(w)/. Logical (zero-fill) shift right by a known amount.
lshr :: NatRepr w -> Domain w -> Integer -> Domain w
lshr w (BVBitInterval mask lo hi) y = BVBitInterval mask (shr lo) (shr hi)
  where
  y' = fromInteger (min y (intValue w))
  shr x = x `shiftR` y'

-- | /O(w)/. Arithmetic (sign-extending) shift right by a known amount.
ashr :: (1 <= w) => NatRepr w -> Domain w -> Integer -> Domain w
ashr w (BVBitInterval mask lo hi) y = BVBitInterval mask (shr lo) (shr hi)
  where
  y' = fromInteger (min y (intValue w))
  shr x = ((toSigned w x) `shiftR` y') .&. mask

-- | Conflict ("empty") domain: invariant @lo [= hi@ is violated.
-- Used as the meet identity when intersecting per-shift contributions.
conflict :: Integer -> Domain w
conflict mask = BVBitInterval mask mask 0

isConflict :: Domain w -> Bool
isConflict (BVBitInterval _ lo hi) = Prelude.not (bitle lo hi)

-- | Is this the fully unknown domain, @[0, mask]@?
isAny :: Domain w -> Bool
isAny (BVBitInterval mask lo hi) = lo == 0 && hi == mask

-- | Decompose @b@'s bounds into two bitmasks, @(zeros, ones)@:
--
-- * @zeros@ has a @1@ at every position where every member of @b@ has a @0@.
-- * @ones@ has a @1@ at every position where every member of @b@ has a @1@.
--
-- This is the same encoding LLVM's @KnownBits@ uses, and is paired with
-- 'memberMask' to check membership using bitwise operations alone.
knownZerosOnes :: Domain w -> (Integer, Integer)
knownZerosOnes (BVBitInterval mask lo hi) = (mask `Bits.xor` hi, lo)

-- | Equivalent to 'member' @b@ @s@, given @(zeros, ones) = knownZerosOnes b@.
-- Cheaper than 'member' (no @[lo, hi]@ ordering check) and lets the inner
-- loop hoist @(zeros, ones)@ outside the iteration.
memberMask :: Integer -> Integer -> Integer -> Bool
memberMask zeros ones s = (zeros .&. s) == 0 && (ones .|. s) == s

-- | Generic shift skeleton shared by 'shlAbstract', 'lshrAbstract', and
-- 'ashrAbstract'.
--
-- The idea: try every concrete shift amount @s@ that @b@ could be, apply
-- @op s@, and union the results. \"Union\" here means \"a result bit is
-- known to be 0 only if every per-shift result agrees it's 0, known to
-- be 1 only if every result agrees it's 1, otherwise unknown\".
--
-- Three optimizations make this fast:
--
-- * Don't iterate past the width. Every shift amount @>= w@ produces
--   the same result for a given @op@ (all zeros for @shl@/@lshr@, the
--   sign-extended pattern for @ashr@), so we iterate
--   @[bl, min bh w]@ and (if @bh > w@) collapse the rest into one
--   call @op w@.
-- * Skip impossible amounts. If @b@'s low bit is known to be 1, only
--   odd shift amounts are reachable; we use 'memberMask' to skip the
--   rest with a cheap pair of bitwise tests.
-- * Stop early. If the running union is already \"fully unknown\",
--   nothing more can be inferred.
--
-- Same iteration strategy as LLVM's @KnownBits::shl@, @KnownBits::lshr@,
-- and @KnownBits::ashr@.
{-# INLINE foldShifts #-}
foldShifts ::
  NatRepr w ->
  Domain w {- ^ shift-amount domain -} ->
  (Int -> Domain w) {- ^ per-shift transfer; @s@ ranges over @[0..w]@ -} ->
  Domain w
foldShifts w b op = collapse (go bl (conflict mask))
  where
  mask = bvdMask b
  wI = intValue w
  (bl, bh) = ubounds b
  (zeros, ones) = knownZerosOnes b
  iterEnd = min bh wI
  go !s !acc
    | isAny acc = acc
    | s <= iterEnd =
        if memberMask zeros ones s
          then go (s + 1) (union acc (op (fromInteger s)))
          else go (s + 1) acc
    | bh > wI =
        -- @b@'s high bound itself is a member of @b@ that exceeds @w@,
        -- so at least one shift amount falls in the saturated tail.
        union acc (op (fromInteger wI))
    | otherwise = acc

  collapse d
    | isConflict d = BVBitInterval mask 0 0
    | otherwise    = d

-- | /O(w²)/. Shift left by an amount drawn from the domain @b@. See
-- 'foldShifts' for the algorithm.
--
-- More precisely, /O(n · w)/ where @w@ is the bitvector width and
-- @n = min(bh − bl + 1, w + 1)@ is the number of candidate shift amounts
-- considered, with @bl@ and @bh@ the unsigned bounds of @b@.
shlAbstract :: NatRepr w -> Domain w -> Domain w -> Domain w
shlAbstract w a@(BVBitInterval mask aLo aHi) b
  -- Fast path: a fully unknown @a@ shifts in zeros at the bottom. Bits
  -- @[0..min bl w - 1]@ are forced to 0 because every concrete shift
  -- amount is at least @bl@ (and shift @>= w@ kills every bit).
  | isAny a =
      let k = fromInteger (min bl (intValue w))
          lowZeros = bit k - 1
      in BVBitInterval mask 0 (mask .&. complement lowZeros)
  | otherwise = foldShifts w b shiftBy
  where
  (bl, _) = ubounds b
  shiftBy s = BVBitInterval mask ((aLo `shiftL` s) .&. mask)
                                 ((aHi `shiftL` s) .&. mask)

-- | /O(w²)/. Logical (zero-fill) shift right by an amount drawn from
-- the domain @b@. See 'foldShifts' for the algorithm.
--
-- More precisely, /O(n · w)/ where @w@ is the bitvector width and
-- @n = min(bh − bl + 1, w + 1)@ is the number of candidate shift amounts
-- considered, with @bl@ and @bh@ the unsigned bounds of @b@.
lshrAbstract :: NatRepr w -> Domain w -> Domain w -> Domain w
lshrAbstract w a@(BVBitInterval mask aLo aHi) b
  -- Fast path: every shift @>= bl@ forces the top @min bl w@ bits of
  -- the result to 0.
  | isAny a =
      let k = fromInteger (min bl (intValue w))
          highMask = mask `shiftR` k
      in BVBitInterval mask 0 highMask
  | otherwise = foldShifts w b shiftBy
  where
  (bl, _) = ubounds b
  shiftBy s = BVBitInterval mask (aLo `shiftR` s) (aHi `shiftR` s)

-- | /O(w²)/. Arithmetic (sign-extending) shift right by an amount drawn
-- from the domain @b@. See 'foldShifts' for the algorithm.
--
-- More precisely, /O(n · w)/ where @w@ is the bitvector width and
-- @n = min(bh − bl + 1, w + 1)@ is the number of candidate shift amounts
-- considered, with @bl@ and @bh@ the unsigned bounds of @b@.
ashrAbstract :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashrAbstract w (BVBitInterval mask aLo aHi) b =
  foldShifts w b shiftBy
  where
  -- Sign-extending shift on the @lo@ and @hi@ bounds independently is
  -- sound: if every member of @a@ has a known-1 at position @i >= sign@,
  -- so does every member's @ashr s@; same for known-0.
  shiftBy s = BVBitInterval mask
                ((toSigned w aLo `shiftR` s) .&. mask)
                ((toSigned w aHi `shiftR` s) .&. mask)

-- | /O(w²)/. Rotate left by an amount drawn from the domain @b@. See
-- 'foldRotates' for the algorithm.
--
-- More precisely, /O(r · w)/ where @w@ is the bitvector width and @r@ is
-- the number of distinct residues mod @w@ that are reachable from @b@
-- (at most @w@).
rolAbstract :: NatRepr w -> Domain w -> Domain w -> Domain w
rolAbstract w (BVBitInterval mask aLo aHi) b = foldRotates w b rotBy fullDom
  where
  -- Fast path: if every residue in @[0, w-1]@ is reachable from @b@,
  -- every output bit could come from any input bit, so the answer is
  -- determined by @a@'s global structure alone.
  fullDom = fullCoverage mask aLo aHi
  rotBy s = BVBitInterval mask
              (Arith.rotateLeft w aLo (toInteger s))
              (Arith.rotateLeft w aHi (toInteger s))

-- | /O(w²)/. Rotate right by an amount drawn from the domain @b@.
-- Mirrors 'rolAbstract'.
--
-- More precisely, /O(r · w)/ where @w@ is the bitvector width and @r@ is
-- the number of distinct residues mod @w@ that are reachable from @b@
-- (at most @w@).
rorAbstract :: NatRepr w -> Domain w -> Domain w -> Domain w
rorAbstract w (BVBitInterval mask aLo aHi) b = foldRotates w b rotBy fullDom
  where
  fullDom = fullCoverage mask aLo aHi
  rotBy s = BVBitInterval mask
              (Arith.rotateRight w aLo (toInteger s))
              (Arith.rotateRight w aHi (toInteger s))

-- | Generic rotate skeleton shared by 'rolAbstract' and 'rorAbstract'.
--
-- Rotating by @s@ is the same as rotating by @s `mod` w@, so we only
-- ever care about @w@ distinct rotation amounts. The trick is figuring
-- out which residues mod @w@ some member of @b@ can produce, then
-- unioning @op r@ over those residues. Two cases:
--
-- * Power-of-two width (the common case): @s `mod` w@ is just the low
--   @log2 w@ bits of @s@. So the reachable residues are exactly the
--   values consistent with @b@'s known bits restricted to those low
--   bits, and we use the same @KnownBits@-style mask check as
--   'foldShifts' to skip residues no member of @b@ can produce. This
--   gives the smallest sound result.
--
-- * Non-power-of-two width: there's no clean correspondence between
--   @b@'s bits and residues mod @w@. We fall back to bounds: the
--   residues reachable from @[bl, bh]@ form a (possibly wrapping)
--   range in @[0, w-1]@, which we iterate without further skipping.
--   Sound, sometimes loose.
--
-- Iteration is always at most @w@ steps, never over the (possibly
-- enormous) integer range @[bl, bh]@.
{-# INLINE foldRotates #-}
foldRotates ::
  NatRepr w ->
  Domain w {- ^ rotate-amount domain -} ->
  (Int -> Domain w) {- ^ per-amount transfer; argument is residue mod @w@ -} ->
  Domain w {- ^ result when all residues are reachable -} ->
  Domain w
foldRotates w b op fullDom
  | Arith.isPow2Integer wI =
      let residueMask = wI - 1
          zerosLow = zeros .&. residueMask
          onesLow = ones .&. residueMask
          allResiduesReachable = zerosLow == 0 && onesLow == 0
          skip r = Prelude.not (memberMask zerosLow onesLow (toInteger r))
      in if allResiduesReachable
           then fullDom
           else iterRanges skip [(0, fromInteger wI - 1)] (conflict mask)
  | otherwise =
      case residueRanges of
        Nothing     -> fullDom
        Just ranges -> iterRanges (\_ -> False) ranges (conflict mask)
  where
  mask = bvdMask b
  wI = intValue w
  (bl, bh) = ubounds b
  (zeros, ones) = knownZerosOnes b

  -- Reduce @[bl, bh]@ mod @w@ to a list of residue ranges in @[0, w-1]@.
  -- @Nothing@ means every residue is reachable; otherwise the list has
  -- one or two ranges (two when the residue range wraps around @0@).
  residueRanges
    | bh - bl + 1 >= wI = Nothing
    | otherwise =
        let (ql, rl) = bl `divMod` wI
            (qh, rh) = bh `divMod` wI
        in if qh == ql
             then Just [(fromInteger rl, fromInteger rh)]
             else Just [(0, fromInteger rh), (fromInteger rl, fromInteger wI - 1)]

  iterRanges _ [] acc = acc
  iterRanges skip ((lo, hi) : rest) acc = iterRanges skip rest (iter skip lo hi acc)

  iter skip !s !hi !acc
    | isAny acc = acc
    | s > hi    = acc
    | skip s    = iter skip (s + 1) hi acc
    | otherwise = iter skip (s + 1) hi (union acc (op s))

-- | Declarative reference: union of @op s@ over every member @s@ of
-- @b@. /O(|b| · w / W)/, exponential in @w@, only suitable as a
-- correctness oracle, not for production.
foldShiftsSpec ::
  Integer  {- ^ mask -} ->
  Domain w {- ^ shift-amount domain -} ->
  (Integer -> Domain w) {- ^ per-amount transfer -} ->
  Domain w
foldShiftsSpec mask b op =
  Prelude.foldr (\s acc -> if member b s then union acc (op s) else acc)
                (conflict mask)
                [0 .. mask]

-- | Declarative reference variant of 'shlAbstract': for every member
-- @y@ of the shift-amount domain, compute the per-shift result and
-- union them all. Strictly slower; used to validate 'shlAbstract'.
shlAbstractSpec :: NatRepr w -> Domain w -> Domain w -> Domain w
shlAbstractSpec w a b = foldShiftsSpec (bvdMask a) b (\y -> shl w a y)

lshrAbstractSpec :: NatRepr w -> Domain w -> Domain w -> Domain w
lshrAbstractSpec w a b = foldShiftsSpec (bvdMask a) b (\y -> lshr w a y)

ashrAbstractSpec :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashrAbstractSpec w a b = foldShiftsSpec (bvdMask a) b (\y -> ashr w a y)

rolAbstractSpec :: NatRepr w -> Domain w -> Domain w -> Domain w
rolAbstractSpec w a b = foldShiftsSpec (bvdMask a) b (\y -> rol w a y)

rorAbstractSpec :: NatRepr w -> Domain w -> Domain w -> Domain w
rorAbstractSpec w a b = foldShiftsSpec (bvdMask a) b (\y -> ror w a y)

-- | The result of rotating @a@ by every position in @[0, w-1]@: each
-- output bit could come from any input bit, so the result is
-- determined by global properties of @a@. It's the all-zeros singleton
-- if @a = {0}@, the all-ones singleton if @a@ is the singleton mask,
-- and fully unknown otherwise.
fullCoverage :: Integer -> Integer -> Integer -> Domain w
fullCoverage mask aLo aHi = BVBitInterval mask outLo outHi
  where
  outHi = if aHi == 0 then 0 else mask
  outLo = if aLo == mask then mask else 0

-- | /O(w)/. Bitwise complement.
not :: Domain w -> Domain w
not (BVBitInterval mask alo ahi) =
  BVBitInterval mask (ahi `Bits.xor` mask) (alo `Bits.xor` mask)

-- | /O(w)/. Bitwise AND of two domains.
and :: Domain w -> Domain w -> Domain w
and (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .&. blo) (ahi .&. bhi)

-- | /O(w)/. Bitwise OR of two domains.
or :: Domain w -> Domain w -> Domain w
or (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .|. blo) (ahi .|. bhi)

-- | /O(w)/. Bitwise XOR of two domains.
xor :: Domain w -> Domain w -> Domain w
xor a@(BVBitInterval mask alo _) b@(BVBitInterval _ blo _) = BVBitInterval mask clo chi
  where
  c   = alo `Bits.xor` blo
  cu  = unknownBits a .|. unknownBits b
  chi = c  .|. cu
  clo = chi `Bits.xor` cu


---------------------------------------------------------------------------------------
-- Bounds and comparisons

-- | /O(1)/. Unsigned bounds for the domain. The low bit-pattern bound is
-- also the unsigned minimum, and the high bit-pattern bound is also the
-- unsigned maximum: setting unknown bits to 0 minimizes, setting them to
-- 1 maximizes.
ubounds :: Domain w -> (Integer, Integer)
ubounds = bitbounds

-- | /O(1)/. The mask with just the sign bit set: @bit (w - 1)@.
signBit :: (1 <= w) => NatRepr w -> Integer
signBit w = bit (widthVal w - 1)
{-# INLINE signBit #-}

-- | /O(w)/. Signed bounds for the domain.
sbounds :: (1 <= w) => NatRepr w -> Domain w -> (Integer, Integer)
sbounds w (BVBitInterval _ lo hi) = (toSigned w lo', toSigned w hi')
  where
  signbit = signBit w
  -- If the sign bit is known (lo and hi agree on it), the bit-pattern
  -- bounds are also the signed bounds. If the sign bit is unknown, the
  -- most-negative value sets the sign bit and clears all other unknowns,
  -- and the most-positive clears the sign bit and sets all other unknowns.
  (lo', hi')
    | (lo .&. signbit) == (hi .&. signbit) = (lo, hi)
    | otherwise = (lo .|. signbit, hi .&. complement signbit)

-- | /O(w)/. Check if all elements in one domain are unsigned-less-than all
-- elements in the other.
ult :: Domain w -> Domain w -> Maybe Bool
ult a b
  | ah < bl  = Just True
  | al >= bh = Just False
  | otherwise = Nothing
  where
  (al, ah) = ubounds a
  (bl, bh) = ubounds b

-- | /O(w)/. Check if all elements in one domain are signed-less-than all
-- elements in the other.
slt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe Bool
slt w a b
  | ah < bl  = Just True
  | al >= bh = Just False
  | otherwise = Nothing
  where
  (al, ah) = sbounds w a
  (bl, bh) = sbounds w b

---------------------------------------------------------------------------------------
-- Arithmetic

-- | Convert a domain into its tristate-number form.
toTnum :: Domain w -> Tnum
toTnum d@(BVBitInterval _ lo _) = Tnum.mk lo (unknownBits d)

-- | Convert a tristate-number back into a domain at the given @bvmask@.
fromTnum :: Integer -> Tnum -> Domain w
fromTnum mask t = BVBitInterval mask v (v .|. Tnum.tnumMask t)
  where v = Tnum.tnumValue t

-- | Internal helper: build a singleton domain when only the mask is known.
mkSingleton :: Integer -> Integer -> Domain w
mkSingleton mask x = BVBitInterval mask x' x'
  where x' = x .&. mask

-- | /O(w)/. Add two bitwise domains.
add :: Domain w -> Domain w -> Domain w
add a@(BVBitInterval mask _ _) b = fromTnum mask (Tnum.add mask (toTnum a) (toTnum b))

-- | /O(w)/. Two's complement negation: @negate a = not a + 1@.
negate :: Domain w -> Domain w
negate a = add (not a) (mkSingleton (bvdMask a) 1)

-- | /O(w)/. Subtract: @sub a b = add a (negate b)@.
sub :: Domain w -> Domain w -> Domain w
sub a b = add a (negate b)

-- | /O(w²)/. Multiply by a constant. Uses 'mulPrecise' since the
-- shift-and-add algorithm gives bit-level precision when one operand
-- is concrete.
scale :: Integer -> Domain w -> Domain w
scale k a = mulPrecise (mkSingleton (bvdMask a) k) a

-- | /O(w)/. Multiply two bitwise domains via interval and trailing-zero
-- analysis. Captures known leading bits (both 0s and 1s) derived from
-- @[aMin*bMin, aMax*bMax]@, plus known trailing zeros from the operands.
--
-- See 'Tnum.mul' for the algorithm. 'mulPrecise' is strictly more
-- precise; this is the cheaper alternative when middle-bit precision
-- doesn't matter.
mul :: Domain w -> Domain w -> Domain w
mul a@(BVBitInterval mask _ _) b =
  fromTnum mask (Tnum.mul mask (toTnum a) (toTnum b))

-- | /O(w²)/. Multiply two bitwise domains, combining the shift-and-add
-- tristate-number algorithm (BPF @tnum_mul@) with the interval and
-- trailing-zero analysis of 'mul'. Strictly at least as precise as 'mul'.
mulPrecise :: Domain w -> Domain w -> Domain w
mulPrecise a@(BVBitInterval mask _ _) b =
  intersection
    (fromTnum mask (Tnum.mulPrecise mask (toTnum a) (toTnum b)))
    (mul a b)

-- | /O(w)/. Unsigned division via interval analysis on the quotient bounds.
-- Assumes the divisor is nonzero.
--
-- Captures known leading bits (both 0s and 1s) derived from
-- @[aMin \`quot\` bMax, aMax \`quot\` bMin]@. When the divisor is a known
-- power of two, the result is exact (bit-level structure of the dividend
-- is preserved, e.g.\ @udiv (any w) (singleton w (2^k))@ has its top @k@
-- bits known zero). 'udivPrecise' is strictly more precise; this is the
-- cheaper alternative when middle-bit precision doesn't matter.
udiv :: Domain w -> Domain w -> Domain w
udiv a@(BVBitInterval mask _ _) b =
  fromTnum mask (Tnum.udiv mask (toTnum a) (toTnum b))

-- | /O(w)/. Unsigned remainder via leading-zero analysis. Assumes the divisor
-- is nonzero.
--
-- The result is bounded above by @min(aMax, bMax - 1)@; bits above that are
-- known zero. (The remainder's lower bound is trivially 0, so the same
-- interval-agreement analysis used in 'udiv' would not yield additional
-- leading bits here.) When the divisor is a known power of two,
-- @urem a (singleton w (2^k))@ is exactly the low @k@ bits of @a@.
urem :: Domain w -> Domain w -> Domain w
urem a@(BVBitInterval mask _ _) b =
  fromTnum mask (Tnum.urem mask (toTnum a) (toTnum b))

-- | /O(w²)/. Unsigned division combining abstract schoolbook long division
-- with the interval analysis of 'udiv'. Assumes the divisor is nonzero.
-- Strictly at least as precise as 'udiv'.
--
-- The result is the 'intersection' of 'udiv' (interval analysis on the
-- quotient bounds, plus an exact path for power-of-two divisors) and the
-- schoolbook result (which captures middle-bit structure that interval
-- analysis can't see, but joins through any undetermined comparison and so
-- loses on power-of-two divisors).
udivPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udivPrecise w a b = intersection (fst (longDivision w a b)) (udiv a b)

-- | /O(w²)/. Unsigned remainder combining schoolbook long division with the
-- leading-zero analysis of 'urem'. Assumes the divisor is nonzero. Strictly
-- at least as precise as 'urem'.
uremPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremPrecise w a b = intersection (snd (longDivision w a b)) (urem a b)

-- | Abstract schoolbook long division: simultaneously computes the
-- quotient and remainder by walking the bits of the dividend from MSB to
-- LSB, maintaining a running partial remainder @r@ as a 'Domain'.
--
-- At each step, @r@ is shifted left and the next bit of the dividend is
-- shifted in. If @r >= b@ definitely, we subtract and set the corresponding
-- bit of the quotient. If @r < b@ definitely, we leave it. If the
-- comparison is undetermined, we union both possibilities into @r@ and
-- leave the quotient bit unknown.
longDivision :: forall w. (1 <= w) => NatRepr w -> Domain w -> Domain w -> (Domain w, Domain w)
longDivision w a b = go (widthVal w - 1) (singleton w 0) (singleton w 0)
  where
  -- Loop from bit (w-1) down to 0. @q@ accumulates the quotient,
  -- @r@ is the partial remainder.
  go :: Int -> Domain w -> Domain w -> (Domain w, Domain w)
  go i q r
    | i < 0     = (q, r)
    | otherwise =
        let r'        = injectBit r (testBit a (fromIntegral i))
            r'MinusB  = sub r' b
            (q'', r'')= case ult r' b of
              Just True  -> (q,                       r')
              Just False -> (setBitDom q i,           r'MinusB)
              Nothing    -> (unknownBitDom q i,       union r' r'MinusB)
        in go (i - 1) q'' r''

  -- Shift @r@ left by 1 and OR in a fresh low bit, whose value is
  -- determined by the @testBit@ result on the dividend.
  injectBit :: Domain w -> Maybe Bool -> Domain w
  injectBit r mb =
    let r1 = shl w r 1
        bit_dom = case mb of
          Just True  -> singleton w 1
          Just False -> singleton w 0
          Nothing    -> range w 0 1
    in or r1 bit_dom

  -- Set bit @i@ of a domain that is known to have bit @i@ = 0 going in
  -- (q starts at 0 and we only ever set bits, so this is safe).
  setBitDom :: Domain w -> Int -> Domain w
  setBitDom (BVBitInterval mask lo hi) i =
    BVBitInterval mask (Bits.setBit lo i) (Bits.setBit hi i)

  -- Mark bit @i@ of a domain as unknown.
  unknownBitDom :: Domain w -> Int -> Domain w
  unknownBitDom (BVBitInterval mask lo hi) i =
    BVBitInterval mask lo (Bits.setBit hi i)

-- | /O(w)/. Signed division (rounds toward zero). Assumes the divisor is
-- nonzero.
--
-- Implemented by splitting each operand on its sign bit into a non-negative
-- \"zero circle\" and a negative \"one circle\", applying 'udiv' to the
-- absolute values, fixing up the sign, and joining the resulting subcases.
sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdiv w = signedOp w udiv flipDiff
  where
  -- For sdiv, the result is negated iff the input signs differ.
  flipDiff sa sb d = if sa == sb then d else negate d

-- | /O(w)/. Signed remainder (sign of dividend). Assumes the divisor is
-- nonzero.
--
-- Implemented like 'sdiv', except the result takes the sign of the dividend
-- rather than the XOR of the input signs. Additionally, leading bits of the
-- result are refined using magnitude bounds: if the dividend is non-negative,
-- the result has leading zeros from both the dividend and divisor magnitude;
-- if negative and nonzero, it has leading ones similarly.
srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w a b = meet base signMagnitudeBound
  where
  base = signedOp w urem flipByDividend a b
  flipByDividend SNeg _ d = negate d
  flipByDividend SNonneg _ d = d
  -- Sign/magnitude refinement (LLVM KnownBits::srem approach):
  -- The srem result is bounded in magnitude by both |dividend| and |divisor|-1.
  -- This translates to known leading zeros/ones.
  mask = maxUnsigned w
  (alo, ahi) = bitbounds a
  (blo, bhi) = bitbounds b
  clzOf x = fromInteger (Arith.clz w x)
  -- countMinSignBits: minimum number of identical sign bits guaranteed in b.
  -- Non-negative: leading zeros come from hi (upper bound on set bits).
  -- Negative: leading ones come from lo (lower bound on set bits).
  bSignBits = case signOf w b of
    Just SNonneg -> clzOf bhi
    Just SNeg    -> clzOf (mask `Bits.xor` blo)
    Nothing      -> 1
  signMagnitudeBound = case signOf w a of
    Just SNonneg ->
      let leadZ = max (clzOf ahi) bSignBits
          hi' = mask `shiftR` leadZ
      in BVBitInterval mask 0 hi'
    Just SNeg
      | Prelude.not (member base 0) ->
          let leadO = clzOf (mask `Bits.xor` alo)
              leading = max leadO bSignBits
              lo' = complement (mask `shiftR` leading) .&. mask
          in BVBitInterval mask lo' mask
    _ -> BVBitInterval mask 0 mask

-- | Helper for signed div/rem: split each operand on its sign bit,
--   call the unsigned operation on the absolute values, fix up the
--   result's sign per the operation's rule, and union all subcases.
signedOp ::
  (1 <= w) =>
  NatRepr w ->
  (Domain w -> Domain w -> Domain w) {- ^ unsigned op on absolute values -} ->
  (Sign -> Sign -> Domain w -> Domain w) {- ^ result fix-up given signs -} ->
  Domain w -> Domain w ->
  Domain w
signedOp w uop fixup a b =
  Prelude.foldr1 union
    [ fixup sa sb (uop (absVal sa a') (absVal sb b'))
    | (sa, a') <- splitSign w a
    , (sb, b') <- splitSign w b
    ]
  where
  absVal SNonneg d = d
  absVal SNeg    d = negate d

data Sign = SNonneg | SNeg
  deriving Eq

-- | If the sign bit is known, return its value; otherwise 'Nothing'.
signOf :: (1 <= w) => NatRepr w -> Domain w -> Maybe Sign
signOf w d =
  case testBit d (fromIntegral (widthVal w - 1)) of
    Just True  -> Just SNeg
    Just False -> Just SNonneg
    Nothing    -> Nothing

-- | Split a domain on its sign bit, returning each restriction tagged with
--   its sign. If the sign bit is already known, returns a singleton list.
splitSign :: (1 <= w) => NatRepr w -> Domain w -> [(Sign, Domain w)]
splitSign w d@(BVBitInterval mask lo hi) =
  case signOf w d of
    Just s  -> [(s, d)]
    Nothing -> [ (SNonneg, BVBitInterval mask lo (hi `Bits.xor` signbit))
               , (SNeg,    BVBitInterval mask (lo .|. signbit) hi)
               ]
  where
  signbit = signBit w

-- | /O(w)/. Like 'udiv', but using the SMT-LIB @FixedSizeBitVectors@ theory's
-- div-by-zero semantics: @bvudiv s 0@ is the all-ones bitvector. See @Note
-- [SMT-LIB division]@ in "What4.Interface" for the design rationale.
udivSmtlib :: (1 <= w) => Domain w -> Domain w -> Domain w
udivSmtlib a b
  | Just 0 <- asSingleton b = mkSingleton mask mask
  | member b 0              = union (udiv a b) (mkSingleton mask mask)
  | otherwise               = udiv a b
  where
  mask = bvdMask a

-- | /O(w)/. Like 'urem', but using the SMT-LIB @FixedSizeBitVectors@ theory's
-- div-by-zero semantics: @bvurem s 0@ is the dividend itself (@s@). See @Note
-- [SMT-LIB division]@ in "What4.Interface" for the design rationale.
uremSmtlib :: (1 <= w) => Domain w -> Domain w -> Domain w
uremSmtlib a b
  | Just 0 <- asSingleton b = a
  | member b 0              = union (urem a b) a
  | otherwise               = urem a b

-- | /O(w)/. Like 'sdiv', but using the SMT-LIB QF_BV logic's div-by-zero
-- convention: @bvsdiv s 0@ is all-ones when @s@ is non-negative and @1@ when
-- @s@ is negative. See @Note [SMT-LIB division]@ in "What4.Interface" for the
-- design rationale.
sdivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdivSmtlib w a b
  | Just 0 <- asSingleton b = sdivByZero w a
  | member b 0              = union (sdiv w a b) (sdivByZero w a)
  | otherwise               = sdiv w a b

-- | The result of @bvsdiv s 0@ as a function of @s@'s sign: all-ones when @s >=
--   0@, @1@ when @s < 0@.
sdivByZero :: (1 <= w) => NatRepr w -> Domain w -> Domain w
sdivByZero w a =
  case signOf w a of
    Just SNonneg -> mkSingleton mask mask
    Just SNeg    -> mkSingleton mask 1
    Nothing      -> union (mkSingleton mask 1) (mkSingleton mask mask)
  where
  mask = bvdMask a

-- | /O(w)/. Like 'srem', but using the SMT-LIB QF_BV logic's div-by-zero
-- convention: @bvsrem s 0@ is the dividend itself (@s@). See @Note [SMT-LIB
-- division]@ in "What4.Interface" for the design rationale.
sremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sremSmtlib w a b
  | Just 0 <- asSingleton b = a
  | member b 0              = union (srem w a b) a
  | otherwise               = srem w a b


---------------------------------------------------------------------------------------
-- Correctness properties

-- | Check that a domain is proper, and that
--   the given value is a member
pmember :: NatRepr n -> Domain n -> Integer -> Bool
pmember n a x = proper n a && member a x

correct_any :: (1 <= n) => NatRepr n -> Integer -> Property
correct_any n x = property (pmember n (any n) x)

correct_singleton :: (1 <= n) => NatRepr n -> Integer -> Integer -> Property
correct_singleton n x y = property (pmember n (singleton n x') y' == (x' == y'))
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_overlap :: Domain n -> Domain n -> Integer -> Property
correct_overlap a b x =
  member a x && member b x ==> domainsOverlap a b

-- | If 'domainsOverlap' returns 'True', then a shared witness exists
-- at the bitwise OR of the two low masks.
correct_overlap_inv :: Domain n -> Domain n -> Property
correct_overlap_inv a b =
  domainsOverlap a b ==> (member a witness && member b witness)
  where
    (alo, _) = bitbounds a
    (blo, _) = bitbounds b
    witness  = alo Bits..|. blo

correct_asSingleton :: (1 <= n) => NatRepr n -> Domain n -> Property
correct_asSingleton n a =
  case asSingleton a of
    Just x -> property (a == singleton n x)
    Nothing -> property True

correct_union :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Integer -> Property
correct_union n a b x =
  member a x || member b x ==> pmember n (union a b) x

correct_intersection :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
correct_intersection a b x = -- NB, intersection might not be proper
  member a x && member b x ==> member (intersection a b) x

correct_join :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Integer -> Property
correct_join n a b x =
  member a x || member b x ==> pmember n (join a b) x

correct_meet :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
correct_meet a b x =
  member a x && member b x ==> member (meet a b) x

-- | Precision of meet: if @x@ is a member of @meet a b@, then @x@ is
-- a member of both @a@ and @b@.
precise_meet :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
precise_meet a b x =
  member (meet a b) x ==> (member a x && member b x)

correct_leq :: Domain n -> Domain n -> Integer -> Property
correct_leq a b x =
  (leq a b && member a x) ==> member b x

------------------------------------------------------------------------
-- Lattice law properties (semantic, i.e. same set of members)

join_commutative :: Domain n -> Domain n -> Integer -> Property
join_commutative a b x =
  property (member (join a b) x == member (join b a) x)

join_idempotent :: Domain n -> Integer -> Property
join_idempotent a x =
  property (member (join a a) x == member a x)

meet_commutative :: Domain n -> Domain n -> Integer -> Property
meet_commutative a b x =
  property (member (meet a b) x == member (meet b a) x)

meet_idempotent :: Domain n -> Integer -> Property
meet_idempotent a x =
  property (member (meet a a) x == member a x)

join_top :: NatRepr n -> Domain n -> Integer -> Property
join_top n a x =
  property (member (join a (top n)) x)

join_bottom :: NatRepr n -> Domain n -> Integer -> Property
join_bottom n a x =
  property (member (join a (bottom n)) x == member a x)

meet_top :: NatRepr n -> Domain n -> Integer -> Property
meet_top n a x =
  property (member (meet a (top n)) x == member a x)

meet_bottom :: NatRepr n -> Domain n -> Integer -> Property
meet_bottom n a x =
  property (Prelude.not (member (meet a (bottom n)) x))

leq_reflexive :: Domain n -> Property
leq_reflexive a = property (leq a a)

join_upper_bound :: Domain n -> Domain n -> Property
join_upper_bound a b = property (leq a (join a b))

join_proper :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
join_proper n a b = property (proper n (join a b))

meet_proper :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
meet_proper n a b = property (proper n c || isBottom c)
  where c = meet a b

correct_zero_ext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_zero_ext w a u x = member a x' ==> pmember u (zext a u) x'
  where
  x' = toUnsigned w x

correct_sign_ext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_sign_ext w a u x = member a x' ==> pmember u (sext w a u) x'
  where
  x' = toSigned w x

correct_concat :: NatRepr m -> (Domain m,Integer) -> NatRepr n -> (Domain n,Integer) -> Property
correct_concat m (a,x) n (b,y) = member a x' ==> member b y' ==> pmember (addNat m n) (concat m a n b) z
  where
  x' = toUnsigned m x
  y' = toUnsigned n y
  z  = x' `shiftL` (widthVal n) .|. y'

correct_shrink :: NatRepr i -> NatRepr n -> (Domain (i + n), Integer) -> Property
correct_shrink i n (a,x) = member a x' ==> pmember n (shrink i a) (x' `shiftR` widthVal i)
  where
  x' = x .&. bvdMask a

correct_trunc :: (n <= w) => NatRepr n -> (Domain w, Integer) -> Property
correct_trunc n (a,x) = member a x' ==> pmember n (trunc n a) (toUnsigned n x')
  where
  x' = x .&. bvdMask a

correct_select :: (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> (Domain w, Integer) -> Property
correct_select i n (a, x) = member a x ==> pmember n (select i n a) y
  where
  y = toUnsigned n ((x .&. bvdMask a) `shiftR` (widthVal i))

correct_eq :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_eq n (a,x) (b,y) =
  member a x ==> member b y ==>
    case eq a b of
      Just True  -> toUnsigned n x == toUnsigned n y
      Just False -> toUnsigned n x /= toUnsigned n y
      Nothing    -> True

correct_shl :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_shl n (a,x) y = member a x ==> pmember n (shl n a y) z
  where
  z = (toUnsigned n x) `shiftL` fromInteger (min (intValue n) y)

correct_lshr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Integer -> Property
correct_lshr n (a,x) y = member a x ==> pmember n (lshr n a y) z
  where
  z = (toUnsigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_ashr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Integer -> Property
correct_ashr n (a,x) y = member a x ==> pmember n (ashr n a y) z
  where
  z = (toSigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_rol :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_rol n (a,x) y = member a x ==> pmember n (rol n a y) (Arith.rotateLeft n x y)

correct_ror :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_ror n (a,x) y = member a x ==> pmember n (ror n a y) (Arith.rotateRight n x y)

correct_shlAbstract ::
  (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_shlAbstract n (a,x) (b,y) =
  member a x ==> member b y ==> pmember n (shlAbstract n a b) z
  where
  z = (toUnsigned n x) `shiftL` fromInteger (min (intValue n) (toUnsigned n y))

correct_lshrAbstract ::
  (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_lshrAbstract n (a,x) (b,y) =
  member a x ==> member b y ==> pmember n (lshrAbstract n a b) z
  where
  z = (toUnsigned n x) `shiftR` fromInteger (min (intValue n) (toUnsigned n y))

correct_ashrAbstract ::
  (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_ashrAbstract n (a,x) (b,y) =
  member a x ==> member b y ==> pmember n (ashrAbstract n a b) z
  where
  z = (toSigned n x) `shiftR` fromInteger (min (intValue n) (toUnsigned n y))

correct_rolAbstract ::
  (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_rolAbstract n (a,x) (b,y) =
  member a x ==> member b y ==>
    pmember n (rolAbstract n a b) (Arith.rotateLeft n x (toUnsigned n y))

correct_rorAbstract ::
  (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_rorAbstract n (a,x) (b,y) =
  member a x ==> member b y ==>
    pmember n (rorAbstract n a b) (Arith.rotateRight n x (toUnsigned n y))

-- | The optimized 'shlAbstract' produces the same domain as the
-- declarative 'shlAbstractSpec'. Together with 'correct_shlAbstract',
-- this proves 'shlAbstract' is point-wise optimal at this domain.
correct_equiv_shlAbstract ::
  (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
correct_equiv_shlAbstract n a b =
  property (shlAbstract n a b == shlAbstractSpec n a b)

correct_equiv_lshrAbstract ::
  (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
correct_equiv_lshrAbstract n a b =
  property (lshrAbstract n a b == lshrAbstractSpec n a b)

correct_equiv_ashrAbstract ::
  (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
correct_equiv_ashrAbstract n a b =
  property (ashrAbstract n a b == ashrAbstractSpec n a b)

correct_equiv_rolAbstract ::
  (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
correct_equiv_rolAbstract n a b =
  property (rolAbstract n a b == rolAbstractSpec n a b)

correct_equiv_rorAbstract ::
  (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
correct_equiv_rorAbstract n a b =
  property (rorAbstract n a b == rorAbstractSpec n a b)

correct_not :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_not n (a,x) = member a x ==> pmember n (not a) (complement x)

correct_and :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_and n (a,x) (b,y) = member a x ==> member b y ==> pmember n (and a b) (x .&. y)

correct_or :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_or n (a,x) (b,y) = member a x ==> member b y ==> pmember n (or a b) (x .|. y)

correct_xor :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_xor n (a,x) (b,y) = member a x ==> member b y ==> pmember n (xor a b) (x `Bits.xor` y)

correct_testBit :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Natural -> Property
correct_testBit n (a,x) i =
  i < natValue n ==>
    case testBit a i of
      Just True  -> Bits.testBit x (fromIntegral i)
      Just False -> Prelude.not (Bits.testBit x (fromIntegral i))
      Nothing    -> True

correct_ubounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_ubounds n (a,x) = member a x' ==> lo <= x' && x' <= hi
  where
  x' = toUnsigned n x
  (lo, hi) = ubounds a

correct_sbounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_sbounds n (a,x) = member a x' ==> lo <= x' && x' <= hi
  where
  x' = toSigned n x
  (lo, hi) = sbounds n a

correct_ult :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_ult n (a,x) (b,y) =
  member a x ==> member b y ==>
    case ult a b of
      Just True  -> toUnsigned n x < toUnsigned n y
      Just False -> toUnsigned n x >= toUnsigned n y
      Nothing    -> True

correct_slt :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_slt n (a,x) (b,y) =
  member a x ==> member b y ==>
    case slt n a b of
      Just True  -> toSigned n x < toSigned n y
      Just False -> toSigned n x >= toSigned n y
      Nothing    -> True

correct_add :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_add n (a,x) (b,y) = member a x ==> member b y ==> pmember n (add a b) (x + y)

correct_sub :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sub n (a,x) (b,y) = member a x ==> member b y ==> pmember n (sub a b) (x - y)

correct_neg :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_neg n (a,x) = member a x ==> pmember n (negate a) (Prelude.negate x)

correct_scale :: (1 <= n) => NatRepr n -> Integer -> (Domain n, Integer) -> Property
correct_scale n k (a,x) = member a x ==> pmember n (scale k' a) (k' * x)
  where
  k' = toSigned n k

correct_mul :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_mul n (a,x) (b,y) = member a x ==> member b y ==> pmember n (mul a b) (x * y)

correct_mulPrecise :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_mulPrecise n (a,x) (b,y) = member a x ==> member b y ==> pmember n (mulPrecise a b) (x * y)

correct_udiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udiv n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (udiv a b) (x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_urem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_urem n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (urem a b) (x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sdiv n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (sdiv n a b) (x' `quot` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_srem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_srem n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (srem n a b) (x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_udivPrecise :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udivPrecise n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (udivPrecise n a b) (x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_uremPrecise :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_uremPrecise n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (uremPrecise n a b) (x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y



correct_udivSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udivSmtlib n (a,x) (b,y) =
  member a x' ==> member b y' ==>
    pmember n (udivSmtlib a b)
      (if y' == 0 then maxUnsigned n else x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_uremSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_uremSmtlib n (a,x) (b,y) =
  member a x' ==> member b y' ==>
    pmember n (uremSmtlib a b) (if y' == 0 then x' else x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdivSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sdivSmtlib n (a,x) (b,y) =
  member a x ==> member b y ==>
    pmember n (sdivSmtlib n a b) result
  where
  x' = toSigned n x
  y' = toSigned n y
  result
    | y' /= 0   = x' `quot` y'
    | x' >= 0   = maxUnsigned n
    | otherwise = 1

correct_sremSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sremSmtlib n (a,x) (b,y) =
  member a x ==> member b y ==>
    pmember n (sremSmtlib n a b) (if y' == 0 then x' else x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y

