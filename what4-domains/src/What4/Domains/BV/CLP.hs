{-|
Module      : What4.Domains.BV.CLP
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Circular linear progressions (CLPs) are an interval-like abstract domain for
bitvectors. A CLP is a tuple @(start, end, stride)@ representing the sequence
of distinct bitvectors visited by walking from @start@ by @stride@ (mod @2^w@)
until reaching @end@:

@
{ start, (start + stride) mod 2^w, (start + 2*stride) mod 2^w, ..., end }
@

Notably, this representation allows for intervals that wrap around, and
even for intervals that wrap around multiple times before reaching @end@
(while still visiting only distinct bitvectors). The interval domain in
"What4.Domains.BV.Arith" can be thought of as a CLP with @stride = 1@.

It is common to conceptualize these progressions as intervals that proceed
clockwise around a \"number circle\", starting at 0 at the south pole,
proceeding around to the signed maximum at the north pole (and then immediately
to the signed minimum), and ending at the unsigned maximum just before 0.

@
smax = 011..1 --vv-- 100..0 = smin
                --
              /    \
              \    /
                --
umin = 000..0 --^^-- 111..1 = umax
@

This module does not define lattice operations and enforces that all of its
inputs and outputs are non-bottom ('proper') CLPs. For a pseudo-lattice
structure on top of CLPs, see "What4.Domains.BV.StridedInteravl"

Related domains in the literature:

* The canonical reference for CLPs is /Executable Analysis using Abstract
  Interpretation with Circular Linear Progressions/. An implementation is
  available at <https://github.com/statinf-otawa/otawa-clp>.
* The /Strided Interval/ (SI) domain from /WYSINWYX: What You See Is Not What
  You Execute/ and /Intermediate-Representation Recovery from Low-Level Code/.
* The /Wrapped Interval/ (WI) domain from /Signedness-Agnostic Program Analysis:
  Precise Integer Bounds for Low-Level Code/ (though this is stride-1).
* The /Signedness-Agnostic Strided Interval/ (SASI) from /BinTrimmer: Towards
  Static Binary Debloating Through Abstract Interpretation/. Implementation
  available at <https://github.com/ucsb-seclab/sasi>.
* Reduced products of congruence and (wrapped) interval domains, e.g., in Crab
  <https://github.com/seahorn/crab/blob/146f5399c72ff508f176e6392e490647ac657ce7/include/crab/domains/interval_congruence.hpp>.

A correctness specification of every operation is given in Cryptol in
@doc\/clp.cry@; the Haskell @correct_*@ predicates here mirror that
specification.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.CLP
  ( Clp
  , start
  , end
  , stride
  , mask
  , proper
  -- * Construction
  , mk
  -- , singleton
  -- , fromRange
  -- , fromFoldable
  -- * Conversion
  , toArith
  , fromArith
  , toBitwise
  , fromBitwise
  -- * Queries
  , member
  , toList
  -- , asSingleton
  -- , size
  -- , eq
  -- , ubounds
  -- , sbounds
  -- , ult
  -- , slt
  -- , overlap
  -- * Arithmetic
  -- , negate
  -- , add
  -- , sub
  -- , scale
  -- , mul
  -- , udiv
  -- , sdiv
  -- , urem
  -- , srem
  -- ** Arithmetic (SMT-LIB div-by-zero semantics)
  -- , udivSmtlib
  -- , uremSmtlib
  -- , sdivSmtlib
  -- , sremSmtlib
  -- * Bitwise operations
  -- , not
  -- , and
  -- , or
  -- , xor
  -- * Concatenation, extension, selection, and truncation
  -- , zext
  -- , sext
  -- , concat
  -- , select
  -- * Shifts and rotations
  -- , shl
  -- , lshr
  -- , ashr
  -- , rol
  -- , ror
  -- * Lattice operations
  -- , top
  -- , bottom
  -- , join
  -- , meet
  -- , leq
  -- * Properties
  -- ** Generators
  , genClp
  , genElement
  , genPair
  -- ** Construction
  -- , correct_singleton
  -- ** Conversion
  , toArithCorrect
  , fromArithCorrect
  , roundtripArith
  , toBitwiseCorrect
  , fromBitwiseCorrect
  -- ** Internal helpers
  , modNegCorrect
  , wrapOffsetCorrect
  , strideGcdDividesStride
  , strideGcdIsPow2
  , divByPow2Correct
  , invModPow2Correct
  , valueIndexCorrect
  , circLeqAtZero
  , circLeqAnchorMin
  , circLeqAnchorMax
  , isMultiWrapViaToList
  -- ** Queries
  -- , correct_asSingleton
  , startMember
  , endMember
  , toListMember
  , memberToList
  , toListNoDuplicates
  -- , correct_eq
  -- , correct_ubounds
  -- , correct_sbounds
  -- , correct_ult
  -- , correct_slt
  -- , correct_overlap
  -- ** Arithmetic
  -- , correct_negate
  -- , correct_add
  -- , correct_sub
  -- , correct_scale
  -- , correct_mul
  -- , correct_udiv
  -- , correct_sdiv
  -- , correct_urem
  -- , correct_srem
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  -- , correct_udivSmtlib
  -- , correct_uremSmtlib
  -- , correct_sdivSmtlib
  -- , correct_sremSmtlib
  -- ** Bitwise operations
  -- , correct_not
  -- , correct_and
  -- , correct_or
  -- , correct_xor
  -- ** Concatenation, extension, selection, and truncation
  -- , correct_zext
  -- , correct_sext
  -- , correct_concat
  -- , correct_select
  -- ** Shifts and rotations
  -- , correct_shl
  -- , correct_lshr
  -- , correct_ashr
  -- , correct_rol
  -- , correct_ror
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.&.), popCount, shiftL, shiftR)
import           GHC.TypeNats (Nat, type (<=))
import           Numeric.Natural (Natural)

import qualified Data.Bits as Bits
import qualified Data.Set as Set

import           Data.Parameterized.NatRepr (NatRepr, maxUnsigned)
import           What4.Domains.Arithmetic (countTrailingZerosOr0, isPow2Natural)
import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInteger)

-- | A 'Clp' represents the set
--
-- @
-- { (start + stride * i) mod mask | i >= 0 s.t. (start + stride * i) <= end }
-- @
--
-- where @mask = 2^w@ for some @w@.
data Clp (w :: Nat)
  = Clp
    { start :: !Natural
    , end :: !Natural
    , stride :: !Natural
    , mask :: !Natural
    }
  deriving (Eq, Ord, Show)

-- | The data-structure invariants of 'Clp'.
proper :: Clp w -> Bool
proper c@Clp {start, end, stride, mask} =
  and
  [ start .&. mask == start
  , end .&. mask == end
  , stride .&. mask == stride
  , stride > 0
  -- @end@ is reachable from @start@ by repeatedly adding @stride@ mod @2^w@.
  , ((end + (mask + 1 - start)) .&. mask) `mod` strideGcd c == 0
  ]

-- ------------------------------------------------------------------
-- * Internal helpers

integerToNatural :: Integer -> Natural
integerToNatural = fromIntegral
{-# INLINE integerToNatural #-}

-- | /O(w)/. Reduce a 'Natural' modulo @2^w@, where @w@ is the width of the CLP.
modMask :: Clp w -> Natural -> Natural
modMask c v = assert (proper c) $ v .&. mask c
{-# INLINE modMask #-}

-- | /O(w)/. Modular additive inverse modulo @mask + 1@.
modNeg :: Natural -> Natural -> Natural
modNeg mask x =
  assert ((mask + 1) .&. mask == 0) $
  assert (x .&. mask == x) $
  (mask + 1 - x) .&. mask
{-# INLINE modNeg #-}

-- | /O(w)/. The wrap-around offset of @v@ from @start@: @(v - start) mod 2^w@.
wrapOffset :: Clp w -> Natural -> Natural
wrapOffset c@Clp{start, mask} v =
  assert (proper c) $ modMask c (v + modNeg mask start)
{-# INLINE wrapOffset #-}

-- | /O(1)/. @gcd(stride, 2^w)@. Since @2^w@ is a power of two, this equals the
-- lowest set bit of @stride@.
strideGcd :: Clp w -> Natural
strideGcd Clp{stride} = 1 `shiftL` countTrailingZerosOr0 (toInteger stride)
{-# INLINE strideGcd #-}

-- | /O(w)/. @x \/ p@ where @p@ is a power of two, computed as a right shift.
-- Asserts that @p@ is a (nonzero) power of two.
divByPow2 :: Natural -> Natural -> Natural
divByPow2 x p =
  assert (isPow2Natural p) $ x `shiftR` popCount (p - 1)
{-# INLINE divByPow2 #-}

-- | /O(w log w)/. Modular inverse of @a@ modulo @m@ where @m@ is a power of two
-- and @a@ is odd. Computed via Hensel lifting (Newton iteration): @x' = x * (2
-- - a*x) mod m@. Each step doubles the number of correct low bits, so the loop
-- runs in @O(log w)@ iterations of @O(w)@ work.
invModPow2 :: Natural -> Natural -> Natural
invModPow2 a m = assert (a `mod` 2 == 1) $ go 1
  where
    mMinus1 = m - 1
    go x =
      let ax = (a * x) .&. mMinus1 in
      if ax == 1
        then x
        else go ((x * (2 + m - ax)) .&. mMinus1)

-- | /O(w log w)/. The progression index of @v@: the unique @i@ in @[0, 2^w \/
-- g)@ such that @start + i*stride ≡ v (mod 2^w)@, where @g = gcd(stride, 2^w)@.
-- Requires @g@ to divide @(v - start) mod 2^w@.
valueIndex :: Clp w -> Natural -> Natural
valueIndex c@Clp{stride, mask} v =
  assert (proper c) $
  assert (off .&. (g - 1) == 0) $
  ((off `divByPow2` g) * sInv) .&. (m' - 1)
  where
    -- @g@ is a power of two (see 'strideGcd'), so all divisions by it (and by
    -- @2^w@) are right shifts.
    off  = wrapOffset c v
    g    = strideGcd c
    m'   = (mask + 1) `divByPow2` g
    sInv = invModPow2 (stride `divByPow2` g) m'

-- | /O(w)/. SASI's @≤_x@: @a ≤_x b@ iff @(a - x) mod 2^w <= (b - x) mod 2^w@.
-- Equivalently, traversing the circle of bitvectors starting at @x@, @a@ is
-- reached no later than @b@.
circLeq :: Natural -> Natural -> Natural -> Natural -> Bool
circLeq m x a b = (a + nx) .&. m <= (b + nx) .&. m
  where nx = modNeg m x

-- | /O(w log w)/. Is this CLP multi-wrap? A CLP is multi-wrap if the
-- cumulative distance traversed by its orbit (@n * stride@, where @n@ is the
-- number of steps from @start@ to @end@) exceeds @2^w@. Geometrically: walking
-- around the number circle from @start@, the orbit passes its starting point
-- two or more times — i.e., the winding number is at least 2.
--
-- Note that all CLP values are distinct by construction (any orbit of length
-- @≤ 2^w \/ gcd(stride, 2^w)@), so multi-wrap does /not/ mean residue classes
-- repeat. It only describes how far the orbit traveled.
isMultiWrap :: Clp w -> Bool
isMultiWrap c@Clp{stride, mask} = valueIndex c (end c) * stride > mask

-- ------------------------------------------------------------------
-- * Construction

-- | Construct a CLP. Asserts that the arguments fit in @w@ bits, that
-- @stride > 0@, and that the resulting CLP is 'proper'.
mk ::
  NatRepr w ->
  -- | @start@
  Natural ->
  -- | @end@
  Natural ->
  -- | @stride@
  Natural ->
  Clp w
mk w s e st =
  assert (s .&. m == s) $
  assert (e .&. m == e) $
  assert (st .&. m == st) $
  assert (st > 0) $
  assert (proper c) c
  where
    m = integerToNatural (maxUnsigned w)
    c = Clp { start = s, end = e, stride = st, mask = m }
{-# INLINE mk #-}

-- ------------------------------------------------------------------
-- * Conversion

-- | /O(w log w)/. Convert a CLP to an arithmetic domain (wrapped interval).
toArith :: Clp w -> A.Domain w
toArith c@Clp{start, end, mask} =
  -- For non-multi-wrap CLPs, the result is the interval @[start, end]@ (over-
  -- approximating by collapsing to stride = 1). For multi-wrap CLPs, the orbit
  -- visits exactly the values congruent to @start@ modulo @g = gcd(stride,
  -- 2^w)@, so we use the tightest such interval: @[start \`mod\` g, mask + 1 -
  -- g + (start \`mod\` g)]@.
  --
  -- TODO: both branches are sound but not always tightest. The smallest sound
  -- interval containing the orbit @{ start + i*stride mod 2^w : 0 <= i <= k }@
  -- is the complement of the largest cyclic gap in that orbit. Even outside
  -- the multi-wrap case, walking @[start, end]@ in stride-direction can wrap
  -- past a smaller-cardinality gap than the one between @end@ and @start@. By
  -- the three-distance (Sós\/Steinhaus) theorem the candidate gap sizes are
  -- determined by the continued-fraction convergents of @stride\/g@ modulo
  -- @2^w\/g@, computable in @O(w)@ steps via Euclidean recursion. See Slater
  -- (1967), "Gaps and steps for the sequence n*theta mod 1".
  if isMultiWrap c
    then A.interval imask r (imask + 1 - toInteger g)
    else A.interval imask istart sz
  where
    imask = toInteger mask
    istart = toInteger start
    iend = toInteger end
    sz = (iend + imask + 1 - istart) .&. imask
    g = strideGcd c
    r = toInteger (start `mod` g)

-- | /O(w)/. Convert an arithmetic domain (wrapped interval) to a CLP.
fromArith :: NatRepr w -> A.Domain w -> Maybe (Clp w)
fromArith w = \case
  A.BVDAny _mask -> Just (mk w 0 (integerToNatural imask) 1)
    where imask = maxUnsigned w
  d | A.isBottom d -> Nothing
    | otherwise -> case A.arithDomainData d of
        Nothing -> Nothing
        Just (lo, sz) -> Just (mk w (integerToNatural lo) (integerToNatural ((lo + sz) .&. imask)) 1)
          where imask = maxUnsigned w

-- TODO: The arith<->bitwise helpers below duplicate
-- 'arithToBitwiseDomain'/'bitwiseToArithDomain' in "What4.Domains.BV". Once
-- those are moved into a common module that 'CLP' can import (e.g. by adding a
-- dep from 'BV.Bitwise' to 'BV.Arith'), inline-call them instead.

-- TODO? Can we do better than just arith-to-bitwise by considering stride?

-- | /O(w log w)/. Convert a CLP to a bitwise domain.
toBitwise :: Clp w -> B.Domain w
toBitwise c = arithToBitwise (toArith c)
  where
    arithToBitwise a =
      let imask = A.bvdMask a in
      case A.arithDomainData a of
        Nothing -> B.interval imask 0 imask
        Just (alo, _) -> B.interval imask lo hi
          where
            u = A.unknowns a
            hi = alo Bits..|. u
            lo = hi `Bits.xor` u

-- | /O(1)/. Convert a bitwise domain to a CLP.
fromBitwise :: NatRepr w -> B.Domain w -> Maybe (Clp w)
fromBitwise w b = fromArith w (bitwiseToArith b)
  where
    bitwiseToArith d =
      let imask = B.bvdMask d
          (lo, hi) = B.bitbounds d
      in A.interval imask lo ((hi - lo) Bits..&. imask)

-- ------------------------------------------------------------------
-- * Queries

-- | /O(w log w)/. Test if the given value is a member of the CLP.
--
-- References:
--
-- * SASI Definition 3, Membership function
--
-- SASI\'s @member@ function is actually broken. Their concretization function
-- matches our 'toList', which means that their intervals can semantically
-- support wrapping around multiple times, but their membership function
-- only supports single-wrap. This is likely due to its heritage from Wrapped
-- Intervals, where multi-wrap of stride-1 intervals would result in saturation.
member :: Clp w -> Natural -> Bool
member c v = assert (proper c) $
  wrapOffset c v `mod` strideGcd c == 0
  && valueIndex c v <= valueIndex c (end c)

-- | /O(2^w \/ g)/, where @g = gcd(stride, 2^w)@. Enumerate the (distinct)
-- elements of a CLP, in the order they are produced by the progression:
-- @start, start + stride, ..., end@ (all mod @2^w@).
--
-- References:
--
-- * CLP Section 3, @conc@
-- * SASI Definition 1, Concretization function
toList :: Clp w -> [Natural]
toList c@Clp{start, end, stride} = assert (proper c) $ go start
  where
    -- Walk by stride mod 2^w, emitting each value, stopping after @end@.
    go v
      | v == end  = [v]
      | otherwise = v : go (modMask c (v + stride))

-- ------------------------------------------------------------------
-- * Generators

-- | Generator for a proper 'Clp' at width @w@.
genClp :: NatRepr w -> Gen (Clp w)
genClp w = do
  let m = integerToNatural (maxUnsigned w)
  s <- integerToNatural <$> chooseInteger (0, toInteger m)
  -- Stride must be in @[1, 2^w - 1]@; we pick from @[1, 2^w]@ and clamp by mask
  -- so that stride is uniformly distributed over [1, 2^w-1] (a stride of 2^w
  -- mod mask = 0 would be improper).
  st <- integerToNatural <$> chooseInteger (1, toInteger m)
  -- Pick the progression index @i@ of @end@, so that
  -- @end = (start + i*stride) mod 2^w@. The orbit length is @2^w \/ g@ where
  -- @g = gcd(stride, 2^w)@.
  let g = st .&. ((m + 1) - st)
  let orbit = (m + 1) `div` g
  i <- integerToNatural <$> chooseInteger (0, toInteger orbit - 1)
  pure (mk w s ((s + i * st) .&. m) st)

-- | Generate a random element of the given (proper) CLP.
genElement :: Clp w -> Gen Natural
genElement c@Clp{start, stride} = do
  -- Pick a progression index in @[0, k]@ where @k@ is the index of @end@.
  let k = valueIndex c (end c)
  i <- integerToNatural <$> chooseInteger (0, toInteger k)
  pure (modMask c (start + i * stride))

-- | Generate a random CLP and an element contained in it.
genPair :: NatRepr w -> Gen (Clp w, Natural)
genPair w = do
  c <- genClp w
  x <- genElement c
  pure (c, x)

-- ------------------------------------------------------------------
-- * Correctness properties

-- ------------------------------------------------------------------
-- ** Internal helpers

-- | @x + modNeg (2^k - 1) x ≡ 0 (mod 2^k)@.
modNegCorrect :: Natural -> Int -> Property
modNegCorrect x k =
  k >= 1 ==> property ((x' + modNeg m x') .&. m == 0)
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | @start + wrapOffset c v ≡ v (mod 2^w)@.
wrapOffsetCorrect :: Clp w -> Natural -> Property
wrapOffsetCorrect c v =
  proper c ==>
    property (modMask c (start c + wrapOffset c v) == modMask c v)

-- | @strideGcd c@ divides @stride c@ and divides @2^w@.
strideGcdDividesStride :: Clp w -> Property
strideGcdDividesStride c =
  proper c ==>
    property (stride c `mod` strideGcd c == 0
           && (mask c + 1) `mod` strideGcd c == 0)

-- | @strideGcd c@ is a power of two (i.e. @g .&. (g - 1) == 0@).
strideGcdIsPow2 :: Clp w -> Property
strideGcdIsPow2 c =
  proper c ==> property (g > 0 && g .&. (g - 1) == 0)
  where g = strideGcd c

-- | @divByPow2 (q * 2^k) (2^k) == q@.
divByPow2Correct :: Natural -> Int -> Property
divByPow2Correct q k =
  k >= 0 ==> property (divByPow2 (q * p) p == q)
  where p = 1 `shiftL` k

-- | @(a * invModPow2 a (2^k)) ≡ 1 (mod 2^k)@ for odd @a@ and @k >= 1@.
invModPow2Correct :: Natural -> Int -> Property
invModPow2Correct a k =
  k >= 1 ==> a `mod` 2 == 1 ==>
    property ((a * invModPow2 a m) `mod` m == 1)
  where m = 1 `shiftL` k

-- | @start + valueIndex c v * stride ≡ v (mod 2^w)@ whenever @v@ is on the
-- progression (i.e. @strideGcd c@ divides @wrapOffset c v@).
valueIndexCorrect :: Clp w -> Natural -> Property
valueIndexCorrect c v =
  proper c ==> wrapOffset c v' `mod` strideGcd c == 0 ==>
    property (modMask c (start c + valueIndex c v' * stride c) == v')
  where v' = modMask c v

-- | @circLeq m 0@ degenerates to ordinary unsigned @<=@.
circLeqAtZero :: Natural -> Natural -> Int -> Property
circLeqAtZero a b k =
  k >= 1 ==> property (circLeq m 0 a' b' == (a' <= b'))
  where
    m  = (1 `shiftL` k) - 1
    a' = a .&. m
    b' = b .&. m

-- | The anchor @x@ is the minimum: @circLeq m x x v@ always holds.
circLeqAnchorMin :: Natural -> Natural -> Int -> Property
circLeqAnchorMin x v k =
  k >= 1 ==> property (circLeq m (x .&. m) (x .&. m) (v .&. m))
  where m = (1 `shiftL` k) - 1

-- | The predecessor of @x@ is the maximum: @circLeq m x v (x - 1)@ always holds.
circLeqAnchorMax :: Natural -> Natural -> Int -> Property
circLeqAnchorMax x v k =
  k >= 1 ==>
    property (circLeq m x' (v .&. m) ((x' + m) .&. m))
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | 'isMultiWrap' agrees with the orbit length: a CLP is multi-wrap iff
-- stepping through every element of 'toList' travels strictly more than @2^w@
-- in total. Concretely, @isMultiWrap c@ iff @(length (toList c) - 1) * stride
-- > 2^w - 1@.
isMultiWrapViaToList :: Clp w -> Property
isMultiWrapViaToList c@Clp{stride, mask} =
  proper c ==> property (isMultiWrap c == (k * stride > mask))
  where
    k = fromIntegral (length (toList c) - 1) :: Natural

-- ------------------------------------------------------------------
-- ** Queries

-- | A CLP always contains its own @start@.
startMember :: Clp w -> Property
startMember c = proper c ==> property (member c (start c))

-- | A CLP always contains its own @end@.
endMember :: Clp w -> Property
endMember c = proper c ==> property (member c (end c))

-- | Every element produced by 'toList' is a member of the CLP.
toListMember :: Clp w -> Property
toListMember c =
  proper c ==> property (Prelude.all (member c) (toList c))

-- | If 'member' returns 'True' for some bitvector @x@, then @x@ appears in
-- 'toList'.
memberToList :: Clp w -> Natural -> Property
memberToList c x =
  proper c ==> (member c x' ==> property (x' `elem` toList c))
  where x' = modMask c x

-- | 'toList' produces no duplicate elements.
toListNoDuplicates :: Clp w -> Property
toListNoDuplicates c = proper c ==> property (noDuplicates (toList c))
  where
    noDuplicates xs = length xs == Set.size (Set.fromList xs)

-- ------------------------------------------------------------------
-- ** Conversion

-- | Every element in a CLP is also in its 'toArith' conversion.
toArithCorrect :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
toArithCorrect _w c x =
  proper c ==> member c x' ==>
    property (A.member (toArith c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in an arithmetic domain is also in its 'fromArith' conversion
-- (when that conversion produces a CLP).
fromArithCorrect :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
fromArithCorrect w a x =
  A.proper w a ==> A.member a x ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

-- | Converting from Arith to CLP and back is exact: the round-tripped domain
-- contains exactly the same elements as the original.
roundtripArith :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
roundtripArith w a x =
  A.proper w a ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (A.member a x == A.member (toArith c) x)

-- | Every element in a CLP is also in its 'toBitwise' conversion.
toBitwiseCorrect :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
toBitwiseCorrect _w c x =
  proper c ==> member c x' ==>
    property (B.member (toBitwise c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in a bitwise domain is also in its 'fromBitwise' conversion
-- (when that conversion produces a CLP).
fromBitwiseCorrect :: (1 <= w) => NatRepr w -> B.Domain w -> Integer -> Property
fromBitwiseCorrect w b x =
  B.proper w b ==> B.member b x ==>
    case fromBitwise w b of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

