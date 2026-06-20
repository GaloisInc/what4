{-|
Module      : What4.Domains.FF
Copyright   : (c) Galois Inc, 2016
License     : BSD3
Maintainer  : rscott@galois.com

Provides an interval-based implementation of finite field abstract domains.

The documentation in this module makes reference to two different orderings on
'Fin' values. We first observe that @'Fin' p@ is isomorphic to one of the
following sets of 'Integer's:

* @{ 0, ..., p - 1 }@. We call this the \"unsigned\" representation, as all
  elements are non-negative.

* { -(p - 1)/2, ..., p/2 }. We call this the \"signed\" representation, as it
  includes some negative elements.

With these definitions in mind, we can define two orderings on 'Fin':

* The unsigned ordering: convert two 'Fin' values to the unsigned representation
  and compare the resulting 'Integer's.

* The signed ordering: convert two 'Fin' values to the signed representation
  and compare the resulting 'Integer's.

In general, we assume the unsigned ordering unless otherwise specified.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.FF
  ( Domain(..)
  , member
  -- , interval
  , size
  -- * Projection functions
  , asSingleton
  {-
  , ubounds
  , sbounds
  , eq
  , slt
  , ult
  , isUltSumCommonEquiv
  , domainsOverlap
  , arithDomainData
  , bitbounds
  , unknowns
  , fillright
  -- * Lattice operations
  , top
  , any
  , bottom
  , isBottom
  , join
  , union
  , meet
  , leq
    -- * Operations
  , singleton
  -}
  , range
    -- ** Arithmetic
  {-
  , add
  , negate
  , scale
  , mul
  -}

  -- * Correctness properties
  , genDomain
  , genElement
  , genPair
  {-
  , correct_any
  , correct_ubounds
  , correct_sbounds
  , correct_singleton
  , correct_overlap
  , correct_overlap_inv
  , correct_asSingleton
  , correct_mulRange
  , correct_union
  , correct_join
  , correct_meet
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
  , leq_transitive
  , join_upper_bound
  , join_proper
  , meet_proper
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_shrink
  , correct_trunc
  , correct_select
  , correct_add
  , correct_neg
  , correct_mul
  , correct_scale
  , correct_scale_eq
  , correct_not
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_eq
  , correct_ult
  , correct_slt
  , correct_isUltSumCommonEquiv
  , correct_unknowns
  , correct_bitbounds
  -}
  ) where

import qualified Data.Bits as Bits
import           Data.Bits hiding (testBit, xor)
import           Data.Parameterized.Fin
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.NatRepr (NatRepr)
import           Data.Type.Equality ((:~:)(..))
import           GHC.TypeNats
import           GHC.Stack

import qualified Prelude
import           Prelude hiding (any, concat, negate, and, or, not)

import qualified What4.Domains.Arithmetic as Arith
import           What4.Domains.Verification ( Property, property, (==>), Gen, chooseInteger )

--------------------------------------------------------------------------------
-- Domain definition

-- | A value of type @'Domain' p@ represents a set of finite field elements of
-- order @p@. Each 'Domain' can represent a single contiguous interval of
-- finite field elements.
data Domain (p :: Nat)
  = FFDAny !(NatRepr p)
  -- ^ The set of all finite field elements of order @p@.
  | FFDNone !(NatRepr p)
  -- ^ The empty set of finite field elements of order @p@.
  | FFDInterval !(NatRepr p) !(Fin p) !(Fin p)
  -- ^ Intervals are represented by a starting value and a size.
  -- @FFDInterval l d@ represents the set of values @x@ such that
  -- @l <= x <= l + d@ in the unsigned representation.
  deriving Show

sameDomain :: Domain p -> Domain p -> Bool
sameDomain (FFDAny _) (FFDAny _) = True
sameDomain (FFDNone _) (FFDNone _) = True
sameDomain (FFDInterval _ x w) (FFDInterval _ x' w') = x == x' && w == w'
sameDomain FFDAny{} _ = False
sameDomain FFDNone{} _ = False
sameDomain FFDInterval{} _ = False

-- | Compute how many concrete elements are in the abstract domain.
size :: Domain p -> Integer
size (FFDAny p) = PN.intValue p
size (FFDNone _) = 0
size (FFDInterval _ _ sz) = toInteger (finToNat sz) + 1

-- | Test if the given finite field element is a member of the abstract domain.
member :: (1 <= p) => Domain p -> Fin p -> Bool
member (FFDAny _) _ = True
member (FFDNone _) _ = False
member (FFDInterval p lo sz) x = subFinModN p x lo <= sz

-- | Random generator for domain values.
genDomain :: forall p. (1 <= p) => NatRepr p -> Gen (Domain p)
genDomain p =
  do let mn = minUnsigned p
     let mx = maxUnsigned p
     lo <- chooseFin p (mn, mx)
     sz <- chooseFin p (mn, mx)
     pure $! interval p lo sz

-- | Generate a random element from a domain.
genElement :: (1 <= p) => Domain p -> Gen (Fin p)
genElement (FFDAny p) = chooseFin p (minUnsigned p, maxUnsigned p)
genElement (FFDNone _) = error "Cannot generate random element of FFDNone"
genElement (FFDInterval p lo sz) =
   do x <- chooseFin p (minUnsigned p, sz)
      pure (addFinModN p x lo)

-- | Generate a random domain and an element contained in that domain.
genPair :: (1 <= p) => NatRepr p -> Gen (Domain p, Fin p)
genPair p =
  do a <- genDomain p
     x <- genElement a
     return (a,x)

--------------------------------------------------------------------------------

-- | An alias for 'maxSigned'.
halfRange :: (1 <= p) => NatRepr p -> Fin p
halfRange = maxSigned

--------------------------------------------------------------------------------
-- Projection functions

-- | Return value if this is a singleton.
asSingleton :: (1 <= p) => Domain p -> Maybe (Fin p)
asSingleton x =
  case x of
    FFDAny{} -> Nothing
    FFDNone{} -> Nothing
    FFDInterval _ xl xd
      | xd == minFin -> Just xl
      | otherwise -> Nothing

isSingletonZero :: (1 <= p) => Domain p -> Bool
isSingletonZero x =
  case x of
    FFDAny{} -> False
    FFDNone{} -> False
    FFDInterval _ xl xd -> xl == minFin && xd == minFin

isFFDAny :: Domain w -> Bool
isFFDAny x =
  case x of
    FFDAny{} -> True
    FFDNone{} -> False
    FFDInterval{} -> False

{-
-- | Return unsigned bounds for domain.
ubounds :: Domain p -> (Fin p, Fin p)
ubounds a =
  case a of
    FFDAny mask -> (0, mask)
    FFDInterval mask al aw
      | ah > mask -> (0, mask)
      | otherwise -> (al, ah)
      where ah = al + aw
-}

{-
-- | Return signed bounds for domain.
sbounds :: (1 <= w) => NatRepr w -> Domain w -> (Integer, Integer)
sbounds w a = (lo - delta, hi - delta)
  where
    delta = halfRange w
    (lo, hi) = ubounds (add a (BVDInterval (bvdMask a) delta 0))

-- | Return the @(lo,sz)@, the low bound and size
--   of the given arithmetic interval.  A value @x@ is in
--   the set defined by this domain iff
--   @(x - lo) `mod` w <= sz@ holds.
--   Returns @Nothing@ if the domain contains all values.
arithDomainData :: Domain w -> Maybe (Integer, Integer)
arithDomainData (BVDAny _) = Nothing
arithDomainData (BVDInterval _ al aw) = Just (al, aw)

-- | Return true if domains contain a common element.
domainsOverlap :: Domain w -> Domain w -> Bool
domainsOverlap a b =
  case a of
    BVDAny _ -> True
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> True
        BVDInterval mask bl bw ->
          diff <= bw || diff + aw > mask
          where diff = (al - bl) .&. mask

eq :: Domain w -> Domain w -> Maybe Bool
eq a b
  | Just x <- asSingleton a
  , Just y <- asSingleton b = Just (x == y)
  | domainsOverlap a b == False = Just False
  | otherwise = Nothing

-- | Check if all elements in one domain are less than all elements in other.
slt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe Bool
slt w a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = sbounds w a
    (b_min, b_max) = sbounds w b

-- | Check if all elements in one domain are less than all elements in other.
ult :: (1 <= w) => Domain w -> Domain w -> Maybe Bool
ult a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = ubounds a
    (b_min, b_max) = ubounds b

-- | Check if @(bvult (bvadd a c) (bvadd b c))@ is equivalent to @(bvult a b)@.
--
-- This is true if and only if for all natural values @i_a@, @i_b@, @i_c@ in
-- @a@, @b@, @c@, either both @i_a + i_c@ and @i_b + i_c@ are less than @2^w@,
-- or both are not. We prove this by contradiction. If @i_a = i_b@, then the
-- property is trivial. Assume that @i_a < i_b@. Then @i_a + i_c < i_b + i_c@.
-- If exactly one of the additions is less than @2^w@, it must be the case that
-- @i_a + i_c < 2^w@ and @0 <= i_b + i_c - 2^w < 2^w@. Since @i_b < 2^w@, it
-- follows that @i_b + i_c < 2^w + i_c@, that @i_b + i_c - 2^w < i_c@, and that
-- @i_b + i_c - 2^w < i_a + i_c@. Thus, for these values of @i_a@, @i_b@, @i_c@,
-- @(bvult a b)@ is true, but @(bvult (bvadd a c) (bvadd b c))@ is false, which
-- is a contradiction.
--
-- We check this property by case analysis on whether @c@ is a single
-- non-wrapping interval, or it wraps around and is a union of two non-wrapping
-- intervals. For a non-wrapping (sub)interval @c'@ of @c@, there are four
-- possible cases:
-- 1. @a@ and @b@ contain a single value.
-- 2. @(bvadd a c')@ and @(bvadd b c')@ do not wrap around for any values in
--    @a@, @b@, @c'@.
-- 3. @(bvadd a c')@ and @(bvadd b c')@ wrap around for all values in @a@, @b@,
--    @c'@.
--
-- This is used to simplify @bvult@.
isUltSumCommonEquiv :: Domain w -> Domain w -> Domain w -> Bool
isUltSumCommonEquiv a b c = if al == ah && bl == bh && al == bl
  then True
  else if cl + cw == ch
    then checkSameWrapInterval cl ch
    else checkSameWrapInterval cl mask && checkSameWrapInterval 0 ch
  where
    (mask, cl, cw) = case c of
      BVDInterval mask' cl' cw' -> (mask', cl', cw')
      BVDAny mask' -> (mask', 0, mask')
    ch = (cl + cw) .&. mask
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    checkSameWrapInterval lo hi =
      ah + hi <= mask && bh + hi <= mask || mask < al + lo && mask < bl + lo

--------------------------------------------------------------------------------
-- Lattice operations

-- | Top element of the lattice: represents all bitvectors of width @w@.
top :: (1 <= w) => NatRepr w -> Domain w
top w = BVDAny (maxUnsigned w)
{-# INLINE top #-}

-- | Represents all values.
{-# DEPRECATED any "Use 'top' instead" #-}
any :: (1 <= w) => NatRepr w -> Domain w
any = top
{-# INLINE any #-}

-- | Bottom element of the lattice for the given mask: represents the empty
-- set of bitvectors. This is an improper domain whose membership predicate
-- is unsatisfiable.
bottomForMask :: Integer -> Domain w
bottomForMask mask = BVDInterval mask 0 (-1)
{-# INLINE bottomForMask #-}

-- | Bottom element of the lattice: represents the empty set of bitvectors.
-- This is an improper domain whose membership predicate is unsatisfiable.
bottom :: (1 <= w) => NatRepr w -> Domain w
bottom w = bottomForMask (maxUnsigned w)
{-# INLINE bottom #-}

-- | Returns 'True' if this domain has no members (i.e., is 'bottom'),
--   detected as an improper interval with negative size.
isBottom :: Domain w -> Bool
isBottom (BVDInterval _ _ sz) = sz < 0
isBottom (BVDAny _) = False

-- | Lattice join (least upper bound) of two domains.
-- If both inputs are proper (or bottom), so is the result.
--
-- For two non-bottom intervals, the result is the shortest single
-- interval containing both. The trick is to compare each interval's
-- \"average value\" @2*lo + sz@ (twice the midpoint, doubled to avoid
-- fractions). If the averages are more than half the modulus apart,
-- the inputs sit on opposite sides of zero, so we lift the smaller-
-- midpoint interval by @2^w@ before taking the enclosing range. This
-- yields the shorter of the two enclosing arcs — the one that wraps
-- around zero when appropriate — rather than always going clockwise.
-- 'interval' then collapses sizes @>= 2^w@ to 'BVDAny'.
--
-- @
--     Visualize the modular number line @[0, mask]@ as a horizontal strip.
--
--     midpoints close — naive convex hull is already optimal:
--            0                                     mask
--     a:     [-----]
--     b:               [-----]
--     naive: [---------------]   (= our result)
--
--     midpoints far apart — naive hull is wasteful, wrapping is shorter:
--            0                                     mask
--     a:     [-----]
--     b:                                   [-----]
--     naive: [-----------------------------------]   (covers nearly everything)
--     ours:  -----]                        [------   (wraps around; tight)
-- @
join :: (1 <= w) => Domain w -> Domain w -> Domain w
join a b | isBottom a = b
         | isBottom b = a
join a@BVDAny{} _ = a
join _ b@BVDAny{} = b
join (BVDInterval mask al aw) (BVDInterval _ bl bw) =
  interval mask cl (ch - cl)
  where
    sz = mask + 1
    ac = 2 * al + aw -- twice the average value of a
    bc = 2 * bl + bw -- twice the average value of b
    -- If the averages are 2^(w-1) or more apart,
    -- then shift the lower interval up by 2^w.
    al' = if ac + mask < bc then al + sz else al
    bl' = if bc + mask < ac then bl + sz else bl
    ah' = al' + aw
    bh' = bl' + bw
    cl = min al' bl'
    ch = max ah' bh'

-- | Return union of two domains.
{-# DEPRECATED union "Use 'join' instead" #-}
union :: (1 <= w) => Domain w -> Domain w -> Domain w
union = join
{-# INLINE union #-}

-- | Lattice meet: an over-approximation of the intersection of two domains.
-- For any concrete value @x@, if @x@ is a member of both @a@ and @b@, then
-- @x@ is a member of @meet a b@.
-- If both inputs are proper (or bottom), so is the result.
meet :: (1 <= w) => Domain w -> Domain w -> Domain w
meet a _ | isBottom a = a
meet _ b | isBottom b = b
meet (BVDAny _) b = b
meet a (BVDAny _) = a
meet a b
  | sameDomain a b = a
meet a b =
  let (al, ah) = ubounds a
      (bl, bh) = ubounds b
      cl = max al bl
      ch = min ah bh
      mask = bvdMask a
  in if cl > ch
     then bottomForMask mask
     else interval mask cl (ch - cl)

-- | Lattice ordering: @leq a b@ returns 'True' if every concrete value
-- represented by @a@ is also represented by @b@.
leq :: Domain w -> Domain w -> Bool
leq a _ | isBottom a = True
leq _ b | isBottom b = False
leq _ (BVDAny _) = True
leq (BVDAny _) (BVDInterval _ _ _) = False
leq (BVDInterval mask al aw) (BVDInterval _ bl bw) =
  ((al - bl) .&. mask) + aw <= bw
{-# INLINE leq #-}

--------------------------------------------------------------------------------
-- Operations

-- | Create a bitvector domain representing the integer.
singleton :: (HasCallStack, 1 <= w) => NatRepr w -> Integer -> Domain w
singleton w x = BVDInterval mask (x .&. mask) 0
  where mask = maxUnsigned w
-}

-- | @range p l h@ returns domain containing all finite field elements in the
-- range @[l, h-l]@.
range :: (1 <= p) => NatRepr p -> Fin p -> Fin p -> Domain p
range p l h = interval p l (subFinModN p h l)

-- | Alias for 'FFDInterval'.
interval :: NatRepr p -> Fin p -> Fin p -> Domain p
interval = FFDInterval

{-
-- | @concat a y@ returns domain where each element in @a@ has been
-- concatenated with an element in @y@.  The most-significant bits
-- are @a@, and the least significant bits are @y@.
concat :: NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u a v b =
  case a of
    BVDAny _ -> BVDAny mask
    BVDInterval _ al aw -> interval mask (cat al bl) (cat aw bw)
  where
    cat i j = (i `shiftL` widthVal v) + j
    mask = maxUnsigned (addNat u v)
    (bl, bh) = ubounds b
    bw = bh - bl

-- | @shrink i a@ drops the @i@ least significant bits from @a@.
shrink ::
  NatRepr i ->
  Domain (i + n) -> Domain n
shrink i a =
  case a of
    BVDAny mask -> BVDAny (shr mask)
    BVDInterval mask al aw ->
      interval (shr mask) bl (bh - bl)
      where
        bl = shr al
        bh = shr (al + aw)
  where
    shr x = x `shiftR` widthVal i

-- | @trunc n d@ selects the @n@ least significant bits from @d@.
trunc ::
  (n <= w) =>
  NatRepr n ->
  Domain w -> Domain n
trunc n a =
  case a of
    BVDAny _ -> BVDAny mask
    BVDInterval _ al aw -> interval mask al aw
  where
    mask = maxUnsigned n

-- | @select i n a@ selects @n@ bits starting from index @i@ from @a@.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  Domain w -> Domain n
select i n a = shrink i (trunc (addNat i n) a)

zext :: (1 <= w, w + 1 <= u) => Domain w -> NatRepr u -> Domain u
zext a u = range u al ah
  where (al, ah) = ubounds a

sext ::
  forall w u. (1 <= w, w + 1 <= u) =>
  NatRepr w ->
  Domain w ->
  NatRepr u ->
  Domain u
sext w a u =
  case fProof of
    LeqProof ->
      range u al ah
      where (al, ah) = sbounds w a
  where
    wProof :: LeqProof 1 w
    wProof = LeqProof
    uProof :: LeqProof (w + 1) u
    uProof = LeqProof
    fProof :: LeqProof 1 u
    fProof = leqTrans (leqAdd wProof (knownNat :: NatRepr 1)) uProof

--------------------------------------------------------------------------------
-- Shifts

shl :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shl w a b
  | isBVDAny a = a
  | isSingletonZero a = a
  | isSingletonZero b = a
  | otherwise = interval mask lo (hi - lo)
    where
      mask = bvdMask a
      sz = mask + 1
      (bl, bh) = ubounds b
      bl' = clamp w bl
      bh' = clamp w bh
      -- compute bounds for c = 2^b
      cl = if (mask `shiftR` bl' == 0) then sz else bit bl'
      ch = if (mask `shiftR` bh' == 0) then sz else bit bh'
      (lo, hi) = mulRange (zbounds a) (cl, ch)

lshr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshr w a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    cl = al `shiftR` clamp w bh
    ch = ah `shiftR` clamp w bl

ashr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashr w a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = sbounds w a
    (bl, bh) = ubounds b
    cl = al `shiftR` (if al < 0 then clamp w bl else clamp w bh)
    ch = ah `shiftR` (if ah < 0 then clamp w bh else clamp w bl)

-- | Clamp the given shift amount to the word width indicated by the
--   nat repr
clamp :: NatRepr w -> Integer -> Int
clamp w x = fromInteger (min (intValue w) x)

--------------------------------------------------------------------------------
-- Arithmetic

add :: (1 <= w) => Domain w -> Domain w -> Domain w
add a b =
  case a of
    BVDAny _ -> a
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> b
        BVDInterval mask bl bw ->
          interval mask (al + bl) (aw + bw)

negate :: (1 <= w) => Domain w -> Domain w
negate a =
  case a of
    BVDAny _ -> a
    BVDInterval mask al aw -> BVDInterval mask ((-ah) .&. mask) aw
      where ah = al + aw

scale :: (1 <= w) => Integer -> Domain w -> Domain w
scale k a
  | k == 0 = BVDInterval (bvdMask a) 0 0
  | k == 1 = a
  | otherwise =
    case a of
      BVDAny _ -> a
      BVDInterval mask al aw
        | k >= 0 -> interval mask (k * al) (k * aw)
        | otherwise -> interval mask (k * ah) (abs k * aw)
        where ah = al + aw

mul :: (1 <= w) => Domain w -> Domain w -> Domain w
mul a b
  | isSingletonZero a = a
  | isSingletonZero b = b
  | isBVDAny a = a
  | isBVDAny b = b
  | otherwise = interval mask cl (ch - cl)
    where
      mask = bvdMask a
      (cl, ch) = mulRange (zbounds a) (zbounds b)

-- | Choose a representative integer range (positive or negative) for
-- the given bitvector domain such that the endpoints are as close to
-- zero as possible.
zbounds :: Domain w -> (Integer, Integer)
zbounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask lo sz -> (lo', lo' + sz)
      where lo' = if 2 * lo + sz > mask then lo - (mask + 1) else lo

mulRange :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
mulRange (al, ah) (bl, bh) = (cl, ch)
  where
    (albl, albh) = scaleRange al (bl, bh)
    (ahbl, ahbh) = scaleRange ah (bl, bh)
    cl = min albl ahbl
    ch = max albh ahbh

scaleRange :: Integer -> (Integer, Integer) -> (Integer, Integer)
scaleRange k (lo, hi)
  | k < 0 = (k * hi, k * lo)
  | otherwise = (k * lo, k * hi)

--------------------------------------------------------------------------------
-- Bitwise logical

-- | Complement bits in range.
not :: Domain w -> Domain w
not a =
  case a of
    BVDAny _ -> a
    BVDInterval mask al aw ->
      BVDInterval mask (complement ah .&. mask) aw
      where ah = al + aw

-- | Return bitwise bounds for domain (i.e. logical AND of all
-- possible values, paired with logical OR of all possible values).
bitbounds :: Domain w -> (Integer, Integer)
bitbounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask al aw
      | al + aw > mask -> (0, mask)
      | otherwise -> (lo, hi)
      where
        au = unknowns a
        hi = al .|. au
        lo = hi `Bits.xor` au

-- | @unknowns lo hi@ returns a bitmask representing the set of bit
-- positions whose values are not constant throughout the range
-- @lo..hi@.
unknowns :: Domain w -> Integer
unknowns (BVDAny mask) = mask
unknowns (BVDInterval mask al aw) = mask .&. (fillright (al `Bits.xor` (al + aw)))

bitle :: Integer -> Integer -> Bool
bitle x y = (x .|. y) == y

-- | @fillright x@ rounds up @x@ to the nearest 2^n-1.
fillright :: Integer -> Integer
fillright = Arith.bitsBelow
{-# INLINE fillright #-}

------------------------------------------------------------------
-- Correctness properties

correct_any :: (1 <= n) => NatRepr n -> Integer -> Property
correct_any w x = property (member w (any w) x)

correct_ubounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_ubounds n (a,x) = member n a x' ==> lo <= x' && x' <= hi
  where
  x' = toUnsigned n x
  (lo,hi) = ubounds a

correct_sbounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_sbounds n (a,x) = member n a x' ==> lo <= x' && x' <= hi
  where
  x' = toSigned n x
  (lo,hi) = sbounds n a

correct_singleton :: (1 <= n) => NatRepr n -> Integer -> Integer -> Property
correct_singleton n x y = property (member n (singleton n x') y' == (x' == y'))
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_overlap :: Domain n -> Domain n -> Integer -> Property
correct_overlap a b x =
  member a x && member b x ==> domainsOverlap a b

-- | If 'domainsOverlap' returns 'True', then a shared witness exists
-- among the low-bound candidates of either domain.
correct_overlap_inv :: Domain n -> Domain n -> Property
correct_overlap_inv a b =
  domainsOverlap a b ==>
    (member a witness && member b witness)
  where
    witness = case (arithDomainData a, arithDomainData b) of
      (Just (alo, _), _) | member b alo -> alo
      (_, Just (blo, _)) -> blo
      _ -> 0

correct_asSingleton :: (1 <= n) => NatRepr n -> Domain n -> Property
correct_asSingleton n a =
  case asSingleton a of
    Just x -> property (a == singleton n x)
    Nothing -> property True

correct_mulRange :: (Integer, Integer) -> (Integer, Integer) -> Integer -> Integer -> Property
correct_mulRange a b x y =
  inRange a x && inRange b y ==> inRange (mulRange a b) (x * y)
  where
    inRange (lo, hi) v = lo <= v && v <= hi

correct_union :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Integer -> Property
correct_union n a b x =
  (member a x || member b x) ==> member n (union a b) x

correct_join :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Integer -> Property
correct_join n a b x =
  (member a x || member b x) ==> member n (join a b) x

correct_meet :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
correct_meet a b x =
  (member a x && member b x) ==> member (meet a b) x

-- Note: 'meet' for the arithmetic domain is *not* a precise intersection
-- when one of the arguments is a wrap-around interval. In that case
-- 'ubounds' returns @(0, mask)@, and the result over-approximates. The
-- bitwise domain's meet (in "What4.Domains.BV.Bitwise") *is* precise; see
-- 'What4.Domains.BV.Bitwise.precise_meet'.

correct_leq :: Domain n -> Domain n -> Integer -> Property
correct_leq a b x =
  (leq a b && member a x) ==> member b x

------------------------------------------------------------------------
-- Lattice law properties (semantic, i.e. same set of members)

join_commutative :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
join_commutative a b x =
  property (member (join a b) x == member (join b a) x)

join_idempotent :: (1 <= n) => Domain n -> Integer -> Property
join_idempotent a x =
  property (member (join a a) x == member a x)

meet_commutative :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
meet_commutative a b x =
  property (member (meet a b) x == member (meet b a) x)

meet_idempotent :: (1 <= n) => Domain n -> Integer -> Property
meet_idempotent a x =
  property (member (meet a a) x == member a x)

join_top :: (1 <= n) => NatRepr n -> Domain n -> Integer -> Property
join_top n a x =
  property (member (join a (top n)) x)

join_bottom :: (1 <= n) => NatRepr n -> Domain n -> Integer -> Property
join_bottom n a x =
  property (member (join a (bottom n)) x == member a x)

meet_top :: (1 <= n) => NatRepr n -> Domain n -> Integer -> Property
meet_top n a x =
  property (member (meet a (top n)) x == member a x)

meet_bottom :: (1 <= n) => NatRepr n -> Domain n -> Integer -> Property
meet_bottom n a x =
  property (Prelude.not (member (meet a (bottom n)) x))

leq_reflexive :: Domain n -> Property
leq_reflexive a = property (leq a a)

leq_transitive :: Domain n -> Domain n -> Domain n -> Property
leq_transitive a b c =
  (leq a b && leq b c) ==> leq a c

join_upper_bound :: (1 <= n) => Domain n -> Domain n -> Property
join_upper_bound a b = property (leq a (join a b))

join_proper :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
join_proper n a b = property (proper n (join a b))

meet_proper :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Property
meet_proper n a b = property (proper n c || isBottom c)
  where c = meet a b

correct_zero_ext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_zero_ext w a u x = member a x' ==> member u (zext a u) x'
  where
  x' = toUnsigned w x

correct_sign_ext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_sign_ext w a u x = member a x' ==> member u (sext w a u) x'
  where
  x' = toSigned w x

correct_concat :: NatRepr m -> (Domain m,Integer) -> NatRepr n -> (Domain n,Integer) -> Property
correct_concat m (a,x) n (b,y) = member a x' ==> member b y' ==> member (addNat m n) (concat m a n b) z
  where
  x' = toUnsigned m x
  y' = toUnsigned n y
  z  = x' `shiftL` (widthVal n) .|. y'

correct_shrink :: NatRepr i -> NatRepr n -> (Domain (i + n), Integer) -> Property
correct_shrink i n (a,x) = member a x' ==> member n (shrink i a) (x' `shiftR` widthVal i)
  where
  x' = x .&. bvdMask a

correct_trunc :: (n <= w) => NatRepr n -> (Domain w, Integer) -> Property
correct_trunc n (a,x) = member a x' ==> member n (trunc n a) (toUnsigned n x')
  where
  x' = x .&. bvdMask a

correct_select :: (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> (Domain w, Integer) -> Property
correct_select i n (a, x) = member a x ==> member n (select i n a) y
  where
  y = toUnsigned n ((x .&. bvdMask a) `shiftR` (widthVal i))

correct_add :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_add n (a,x) (b,y) = member a x ==> member b y ==> member n (add a b) (x + y)

correct_neg :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_neg n (a,x) = member a x ==> member n (negate a) (Prelude.negate x)

correct_not :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_not n (a,x) = member a x ==> member n (not a) (complement x)

correct_mul :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_mul n (a,x) (b,y) = member a x ==> member b y ==> member n (mul a b) (x * y)

correct_scale :: (1 <= n) => NatRepr n -> Integer -> (Domain n, Integer) -> Property
correct_scale n k (a,x) = member a x ==> member n (scale k' a) (k' * x)
  where
  k' = toSigned n k

correct_scale_eq :: (1 <= n) => NatRepr n -> Integer -> Domain n -> Property
correct_scale_eq n k a = property $ sameDomain (scale k' a) (mul (singleton n k) a)
  where
  k' = toSigned n k

correct_udiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udiv n (a,x) (b,y) = member a x' ==> member b y' ==> y' /= 0 ==> member n (udiv a b) (x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_urem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_urem n (a,x) (b,y) = member a x' ==> member b y' ==> y' /= 0 ==> member n (urem a b) (x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdivRange :: (Integer, Integer) -> (Integer, Integer) -> Integer -> Integer -> Property
correct_sdivRange a b x y =
   mem a x ==> mem b y ==> y /= 0 ==> mem (sdivRange a b') (x `quot` y)
 where
 b' = ReciprocalRange (snd b) (fst b)
 mem (lo,hi) v = lo <= v && v <= hi

correct_sdiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sdiv n (a,x) (b,y) =
    member a x ==> member b y ==> y /= 0 ==> member n (sdiv n a b) (x' `quot` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_srem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_srem n (a,x) (b,y) =
    member a x ==> member b y ==> y /= 0 ==> member n (srem n a b) (x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_udivSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udivSmtlib n (a,x) (b,y) =
    member a x' ==> member b y' ==>
      member n (udivSmtlib a b)
        (if y' == 0 then maxUnsigned n else x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_uremSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_uremSmtlib n (a,x) (b,y) =
    member a x' ==> member b y' ==>
      member n (uremSmtlib a b) (if y' == 0 then x' else x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdivSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sdivSmtlib n (a,x) (b,y) =
    member a x ==> member b y ==>
      member n (sdivSmtlib n a b) result
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
      member n (sremSmtlib n a b) (if y' == 0 then x' else x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_shl :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_shl n (a,x) (b,y) = member a x ==> member b y ==> member n (shl n a b) z
  where
  z = (toUnsigned n x) `shiftL` fromInteger (min (intValue n) y)

correct_lshr :: (1 <= n) => NatRepr n ->  (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_lshr n (a,x) (b,y) = member a x ==> member b y ==> member n (lshr n a b) z
  where
  z = (toUnsigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_ashr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_ashr n (a,x) (b,y) = member a x ==> member b y ==> member n (ashr n a b) z
  where
  z = (toSigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_eq :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_eq n (a,x) (b,y) =
  member a x ==> member b y ==>
    case eq a b of
      Just True  -> toUnsigned n x == toUnsigned n y
      Just False -> toUnsigned n x /= toUnsigned n y
      Nothing    -> True

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

correct_isUltSumCommonEquiv ::
  (1 <= n) =>
  NatRepr n ->
  (Domain n, Integer) ->
  (Domain n, Integer) ->
  (Domain n, Integer) ->
  Property
correct_isUltSumCommonEquiv n (a, x) (b, y) (c, z) =
  member a x ==> member b y ==> member c z ==>
    isUltSumCommonEquiv a b c ==>
      ((toUnsigned n (x + z) < toUnsigned n (y + z)) == (toUnsigned n x < toUnsigned n y))

correct_unknowns :: (1 <= n) => Domain n -> Integer -> Integer -> Property
correct_unknowns a x y = member a x ==> member a y ==> ((x .|. u) == (y .|. u)) && (u .|. mask == mask)
  where
  u = unknowns a
  mask = bvdMask a

correct_bitbounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_bitbounds n (a,x) =
    member a x ==> (bitle lo x' && bitle x' hi && bitle hi (maxUnsigned n))
  where
  x' = toUnsigned n x
  (lo, hi) = bitbounds a
-}

------------------------------------------------------------------------
-- Fin utilities

-- | The smallest possible value in the unsigned representation.
minUnsigned :: (1 <= p) => NatRepr p -> Fin p
minUnsigned _ = minFin

-- | The largest possible value in the unsigned representation.
maxUnsigned :: (1 <= p) => NatRepr p -> Fin p
maxUnsigned p
  | Refl <- PN.minusPlusCancel p (PN.knownNat @1)
  = mkFin (PN.decNat p)

-- | The smallest possible value in the signed representation.
minSigned :: (1 <= p) => NatRepr p -> Fin p
minSigned p =
  negFinModN p (finFromNatModN p (PN.natValue (PN.decNat p) `div` 2))

-- | The largest possible value in the signed representation.
maxSigned :: (1 <= p) => NatRepr p -> Fin p
maxSigned p = finFromNatModN p (PN.natValue p `div` 2)

-- | Convert a 'Fin' value to an 'Integer' in the unsigned representation.
finToInteger :: (1 <= p) => NatRepr p -> Fin p -> Integer
finToInteger _ = toInteger . finToNat

-- | Convert a 'Fin' value to an 'Integer' in the signed representation.
finToSignedInteger :: (1 <= p) => NatRepr p -> Fin p -> Integer
finToSignedInteger p x
  | i > PN.maxSigned p
  = i - PN.intValue p
  | otherwise
  = i
  where
    i = finToInteger p x

-- | Convert an 'Integer' (in the unsigned or signed representation) to a 'Fin'
-- value.
finFromInteger :: (1 <= p) => NatRepr p -> Integer -> Fin p
finFromInteger p i
  | i >= 0
  = finFromNatModN p (fromInteger i)
  | otherwise
  = negFinModN p (finFromNatModN p (- (fromInteger i)))

-- | A test generator that returns a 'Fin' value between the specified
-- (inclusive) bounds in the unsigned representation.
chooseFin :: (1 <= p) => NatRepr p -> (Fin p, Fin p) -> Gen (Fin p)
chooseFin p (lo, hi) =
  do x <- chooseInteger (finToInteger p lo, finToInteger p hi)
     pure (finFromInteger p x)
