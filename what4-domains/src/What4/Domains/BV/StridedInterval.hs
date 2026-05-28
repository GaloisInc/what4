{-|
Module      : What4.Domains.BV.StridedInterval
Copyright   : (c) Galois Inc, 2026
License     : BSD3

An interval-like abstract domain for bitvectors based on circular linear
progressions ("What4.Domains.BV.CLP").

Note that this domain does not form a true lattice as it has no associative join
operation (see /Signedness-Agnostic Program Analysis: Precise Integer Bounds
for Low-Level Code/). In fact, *no* domain based on wrapping intervals can
support a true associative join. This could be fixed with a restriction that the
range of values traversed by the CLP doesn't exceed 2^w (it doesn't wrap around
multiple times), but this would lose precision. As associativity of join is not
a soundness property, we choose to keep the precision (matching prior work like
/WI/ and /SASI/, see "What4.Domains.BV.CLP").

A correctness specification of every operation is given in Cryptol in
@doc\/strideddomain.cry@; the Haskell @correct_*@ predicates here mirror that
specification.

Most operations are implemented by converting to either the arithmetic or
bitwise domain, applying the corresponding operation there, and converting
back. This loses precision (the round-trip collapses any non-trivial stride),
but is sound.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.StridedInterval
  ( Domain
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
  , isBottom
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
  , negate
  , add
  , scale
  , mul
  , udiv
  , sdiv
  , urem
  , srem
  -- ** Arithmetic (SMT-LIB div-by-zero semantics)
  , udivSmtlib
  , uremSmtlib
  , sdivSmtlib
  , sremSmtlib
  -- * Bitwise operations
  , not
  , and
  , or
  , xor
  -- * Concatenation, extension, selection, and truncation
  , zext
  , sext
  , concat
  , select
  -- * Shifts and rotations
  , shl
  , lshr
  , ashr
  , rol
  , ror
  -- * Lattice operations
  , top
  , bottom
  , join
  , meet
  -- , leq
  -- * Properties
  -- ** Generators
  , genDomain
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
  -- ** Queries
  -- , correct_asSingleton
  , memberBottom
  , toListMember
  , memberToList
  -- , correct_eq
  -- , correct_ubounds
  -- , correct_sbounds
  -- , correct_ult
  -- , correct_slt
  -- , correct_overlap
  -- ** Arithmetic
  , correct_neg
  , correct_add
  , correct_scale
  , correct_mul
  , correct_udiv
  , correct_sdiv
  , correct_urem
  , correct_srem
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  , correct_udivSmtlib
  , correct_uremSmtlib
  , correct_sdivSmtlib
  , correct_sremSmtlib
  -- ** Bitwise operations
  , correct_not
  , correct_and
  , correct_or
  , correct_xor
  -- ** Concatenation, extension, selection, and truncation
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_select
  -- ** Shifts and rotations
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
  -- ** Lattice operations
  -- *** Join
  , correct_join
  , joinCommutative
  , joinIdempotent
  , joinTop
  , joinBottom
  -- *** Meet
  , correct_meet
  , meetCommutative
  , meetIdempotent
  , meetTop
  , meetBottom
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.&.))
import qualified Data.Bits as Bits
import           GHC.TypeNats (Nat, type (+), type (<=))
import           Numeric.Natural (Natural)
import           Prelude hiding (negate, not, and, or, concat)
import qualified Prelude

import           Data.Parameterized.NatRepr (NatRepr, LeqProof(..))
import qualified Data.Parameterized.NatRepr as NR
import qualified What4.Domains.Arithmetic as Arith
import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.CLP as CLP
import           What4.Domains.BV.CLP (Clp)
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseBool)

-- | A value of type @'Domain' w@ represents a set of bitvectors of width @w@.
-- The set is either empty ('BVDBot'), or a circular linear progression ('Clp').
data Domain (w :: Nat)
  = BVDBot !Natural
    -- ^ The empty set. The argument caches @2^w-1@.
  | BVDClp {-# UNPACK #-} !(Clp w)
  deriving (Eq, Ord, Show)
-- A note on the representation: Instead of representing bottom with improper
-- CLPs (e.g., with stride = 0), we add an explicit 'BVDBot' constructor.
-- This (a) makes it easier to enforce the invariant that operations in the
-- CLP module always return proper CLPs, and (b) speeds up operations in
-- this module. This is because GHC will use pointer tagging in the layout of
-- 'Domain': pointers to 'BVDBot' will have a specific value in the low bits,
-- allowing for pattern matching without loads.

-- ------------------------------------------------------------------
-- * Internal helpers

-- | Dispatch a unary 'Clp' operation through 'Domain': pass 'BVDBot' through
-- unchanged (preserving its cached mask), otherwise apply @f@ on the underlying
-- 'Clp'.
liftClp1 ::
  (Clp w -> Clp w) ->
  Domain w -> Domain w
liftClp1 _ d@(BVDBot _) = d
liftClp1 f (BVDClp c)   = mk (f c)
{-# INLINE liftClp1 #-}

-- | Dispatch a binary 'Clp' operation through 'Domain'. As with 'liftClp1',
-- 'BVDBot' is propagated unchanged when either argument is bottom.
liftClp2 ::
  (Clp w -> Clp w -> Clp w) ->
  Domain w -> Domain w -> Domain w
liftClp2 _ d@(BVDBot _) _ = d
liftClp2 _ _ d@(BVDBot _) = d
liftClp2 f (BVDClp a) (BVDClp b) = mk (f a b)
{-# INLINE liftClp2 #-}

-- ------------------------------------------------------------------
-- * Construction

-- | /O(1)/. Wrap a 'Clp' as a 'Domain'. Asserts that the CLP is 'CLP.proper'.
mk :: Clp w -> Domain w
mk c = assert (CLP.proper c) (BVDClp c)
{-# INLINE mk #-}

-- ------------------------------------------------------------------
-- * Conversion

-- | /O(1)/. Convert a strided interval domain to an arithmetic domain.
--
-- The conversion is sound: every element in the strided interval is also in the
-- result. For stride-1 CLPs, the result is exact; otherwise, it
-- over-approximates.
toArith :: (1 <= w) => NatRepr w -> Domain w -> A.Domain w
toArith w = \case
  BVDBot _mask -> A.bottom w
  BVDClp c -> CLP.toArith c

-- | /O(1)/. Convert an arithmetic domain to a strided interval domain.
--
-- The conversion is exact for non-bottom intervals, producing a stride-1 CLP.
-- 'A.BVDAny' and bottom are converted to 'BVDBot' since CLPs cannot represent
-- full or empty sets in the lattice structure.
fromArith :: (1 <= w) => NatRepr w -> A.Domain w -> Domain w
fromArith w a = case CLP.fromArith w a of
  Nothing -> bottom w
  Just c  -> mk c

-- | /O(w log w)/. Convert a strided interval domain to a bitwise domain.
toBitwise :: (1 <= w) => NatRepr w -> Domain w -> B.Domain w
toBitwise w = \case
  BVDBot _ -> B.bottom w
  BVDClp c -> CLP.toBitwise c

-- | /O(1)/. Convert a bitwise domain to a strided interval domain.
fromBitwise :: (1 <= w) => NatRepr w -> B.Domain w -> Domain w
fromBitwise w b = case CLP.fromBitwise w b of
  Nothing -> bottom w
  Just c  -> mk c

-- ------------------------------------------------------------------
-- * Queries

-- | /O(1)/. Is this domain the empty set?
isBottom :: Domain w -> Bool
isBottom = \case
  BVDBot _ -> True
  BVDClp _ -> False
{-# INLINE isBottom #-}

-- | /O(w)/. Test if the given value is a member of the domain.
member :: Domain w -> Natural -> Bool
member d x = case d of
  BVDBot _ -> False
  BVDClp c -> CLP.member c x
{-# INLINE member #-}

-- | /O(2^w)/. Enumerate the members of the domain.
toList :: Domain w -> [Natural]
toList = \case
  BVDBot _ -> []
  BVDClp c -> CLP.toList c
{-# INLINE toList #-}

-- ------------------------------------------------------------------
-- * Arithmetic

negate :: (1 <= w) => NatRepr w -> Domain w -> Domain w
negate w = liftClp1 (CLP.negate w)

add :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
add w = liftClp2 (CLP.add w)

scale :: (1 <= w) => NatRepr w -> Integer -> Domain w -> Domain w
scale w k = liftClp1 (CLP.scale w k)

mul :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mul w = liftClp2 (CLP.mul w)

udiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udiv w = liftClp2 (CLP.udiv w)

urem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
urem w = liftClp2 (CLP.urem w)

sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdiv w = liftClp2 (CLP.sdiv w)

srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w = liftClp2 (CLP.srem w)

-- ------------------------------------------------------------------
-- ** Arithmetic (SMT-LIB div-by-zero semantics)

udivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udivSmtlib w = liftClp2 (CLP.udivSmtlib w)

uremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremSmtlib w = liftClp2 (CLP.uremSmtlib w)

sdivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdivSmtlib w = liftClp2 (CLP.sdivSmtlib w)

sremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sremSmtlib w = liftClp2 (CLP.sremSmtlib w)

-- ------------------------------------------------------------------
-- * Bitwise operations

not :: (1 <= w) => NatRepr w -> Domain w -> Domain w
not w = liftClp1 (CLP.not w)

and :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
and w = liftClp2 (CLP.and w)

or :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
or w = liftClp2 (CLP.or w)

xor :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
xor w = liftClp2 (CLP.xor w)

-- ------------------------------------------------------------------
-- * Concatenation, extension, selection, and truncation

zext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
zext w d u = case d of
  BVDBot _ -> bottom u
  BVDClp c -> mk (CLP.zext w c u)

sext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w d u = case d of
  BVDBot _ -> bottom u
  BVDClp c -> mk (CLP.sext w c u)

concat ::
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      case (a, b) of
        (BVDBot _, _) -> bottom (NR.addNat u v)
        (_, BVDBot _) -> bottom (NR.addNat u v)
        (BVDClp ca, BVDClp cb) -> mk (CLP.concat u ca v cb)

select ::
  (1 <= n, 1 <= w, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Domain n
select i n w d = case d of
  BVDBot _ -> bottom n
  BVDClp c -> mk (CLP.select i n w c)

-- ------------------------------------------------------------------
-- * Shifts and rotations

shl :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shl w = liftClp2 (CLP.shl w)

lshr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshr w = liftClp2 (CLP.lshr w)

ashr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashr w = liftClp2 (CLP.ashr w)

rol :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rol w = liftClp2 (CLP.rol w)

ror :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ror w = liftClp2 (CLP.ror w)

-- ------------------------------------------------------------------
-- * Lattice operations

-- | /O(1)/. The empty set at width @w@.
bottom :: NatRepr w -> Domain w
bottom w = BVDBot (fromInteger (NR.maxUnsigned w))
{-# INLINE bottom #-}

-- | /O(w)/. The full set at width @w@.
top :: (1 <= w) => NatRepr w -> Domain w
top w = fromArith w (A.top w)
{-# INLINE top #-}

-- | /O(w)/. Lattice join (least upper bound).
join :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
join _ (BVDBot _) e = e
join _ d (BVDBot _) = d
join w (BVDClp a) (BVDClp b) =
  fromArith w (A.join (CLP.toArith a) (CLP.toArith b))

-- | /O(w)/. Lattice meet: a sound /over/-approximation of the
-- intersection of two domains. For any concrete value @x@, if @x@ is
-- a member of both @a@ and @b@, then @x@ is a member of @meet a b@.
meet :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
meet w a b = fromArith w (A.meet (toArith w a) (toArith w b))

-- ------------------------------------------------------------------
-- * Generators

-- | Generator for 'Domain' at width @w@.
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w = do
  isBot <- chooseBool
  if isBot
    then pure (bottom w)
    else mk <$> CLP.genClp w

-- | Generate a member of a non-bottom domain. Calling this on 'BVDBot' is a
-- programmer error since bottom has no elements.
genElement :: Domain w -> Gen Natural
genElement = \case
  BVDBot _ -> error "What4.Domains.BV.StridedInterval.genElement: BVDBot"
  BVDClp c -> CLP.genElement c

-- | Generate a domain together with a member of that domain. To allow
-- generating an element, this never produces 'BVDBot'.
genPair :: NatRepr w -> Gen (Domain w, Natural)
genPair w = do
  (c, x) <- CLP.genPair w
  pure (mk c, x)

-- ------------------------------------------------------------------
-- * Correctness properties

-- ------------------------------------------------------------------
-- ** Queries

-- | 'bottom' has no members.
memberBottom :: NatRepr w -> Natural -> Property
memberBottom w x = property (Prelude.not (member (bottom w) x))

-- | Every element produced by 'toList' is a member.
toListMember :: Domain w -> Property
toListMember d = property (Prelude.all (member d) (toList d))

-- | If 'member' returns 'True', the value appears in 'toList'.
memberToList :: Domain w -> Natural -> Property
memberToList d x = case d of
  BVDBot _ -> property True
  BVDClp c -> CLP.memberToList c x

-- ------------------------------------------------------------------
-- ** Conversion

-- | Every element in a strided interval is also in its 'toArith' conversion.
toArithCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toArithCorrect w d x =
  member d x ==> property (A.member (toArith w d) (toInteger x))

-- | Every element in an arithmetic domain is also in its 'fromArith' conversion.
fromArithCorrect :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
fromArithCorrect w a x =
  A.proper w a ==> A.member a x ==>
    property (member (fromArith w a) (fromIntegral (x .&. NR.maxUnsigned w)))

-- | Converting from Arith to strided interval and back is exact: the
-- round-tripped domain contains exactly the same elements as the original.
roundtripArith :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
roundtripArith w a x =
  A.proper w a ==>
    property (A.member a x == A.member (toArith w (fromArith w a)) x)

-- | Every element in a strided interval is also in its 'toBitwise' conversion.
toBitwiseCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toBitwiseCorrect w d x =
  member d x ==> property (B.member (toBitwise w d) (toInteger x))

-- | Every element in a bitwise domain is also in its 'fromBitwise' conversion.
fromBitwiseCorrect :: (1 <= w) => NatRepr w -> B.Domain w -> Integer -> Property
fromBitwiseCorrect w b x =
  B.proper w b ==> B.member b x ==>
    property (member (fromBitwise w b) (fromIntegral (x .&. NR.maxUnsigned w)))

-- ------------------------------------------------------------------
-- ** Arithmetic

correct_neg :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_neg w d x =
  member d x ==> property (member (negate w d) (asN w (Prelude.negate (toInteger x))))

correct_add ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_add w a x b y =
  member a x ==> member b y ==>
    property (member (add w a b) (asN w (toInteger x + toInteger y)))

correct_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> Domain w -> Natural -> Property
correct_scale w k d x =
  member d x ==> property (member (scale w k d) (asN w (k * toInteger x)))

correct_mul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mul w a x b y =
  member a x ==> member b y ==>
    property (member (mul w a b) (asN w (toInteger x * toInteger y)))

correct_udiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udiv w a x b y =
  member a x ==> member b y ==> y /= 0 ==>
    property (member (udiv w a b) (x `quot` y))

correct_urem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_urem w a x b y =
  member a x ==> member b y ==> y /= 0 ==>
    property (member (urem w a b) (x `rem` y))

correct_sdiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdiv w a x b y =
  member a x ==> member b y ==> y' /= 0 ==>
    property (member (sdiv w a b) (asN w (xs `quot` ys)))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    y' = ys

correct_srem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_srem w a x b y =
  member a x ==> member b y ==> y' /= 0 ==>
    property (member (srem w a b) (asN w (xs `rem` ys)))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    y' = ys

-- ------------------------------------------------------------------
-- *** Arithmetic (SMT-LIB div-by-zero semantics)

correct_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivSmtlib w a x b y =
  member a x ==> member b y ==>
    property (member (udivSmtlib w a b) z)
  where
    z = if y == 0
          then fromInteger (NR.maxUnsigned w)
          else x `quot` y

correct_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_uremSmtlib w a x b y =
  member a x ==> member b y ==>
    property (member (uremSmtlib w a b) z)
  where
    z = if y == 0 then x else x `rem` y

correct_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdivSmtlib w a x b y =
  member a x ==> member b y ==>
    property (member (sdivSmtlib w a b) (asN w z))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    z  = if ys == 0
           then if xs >= 0 then -1 else 1
           else xs `quot` ys

correct_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sremSmtlib w a x b y =
  member a x ==> member b y ==>
    property (member (sremSmtlib w a b) (asN w z))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    z  = if ys == 0 then xs else xs `rem` ys

-- ------------------------------------------------------------------
-- ** Bitwise operations

correct_not :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_not w d x =
  member d x ==> property (member (not w d) (asN w (Bits.complement (toInteger x))))

correct_and ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_and w a x b y =
  member a x ==> member b y ==> property (member (and w a b) (x Bits..&. y))

correct_or ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_or w a x b y =
  member a x ==> member b y ==> property (member (or w a b) (x Bits..|. y))

correct_xor ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_xor w a x b y =
  member a x ==> member b y ==> property (member (xor w a b) (Bits.xor x y))

-- ------------------------------------------------------------------
-- ** Concatenation, extension, selection, and truncation

correct_zero_ext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_zero_ext w d u x =
  member d x ==> property (member (zext w d u) x)

correct_sign_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_sign_ext w d u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      member d x ==> property (member (sext w d u) (asN u (toSigned w (toInteger x))))

correct_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> Natural ->
  NatRepr v -> Domain v -> Natural ->
  Property
correct_concat u a x v b y =
  case NR.leqAddPos u v of
    LeqProof ->
      let z = (x `Bits.shiftL` NR.widthVal v) Bits..|. y in
      member a x ==> member b y ==>
        property (member (concat u a v b) z)

correct_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Natural -> Property
correct_select i n w d x =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n) (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      let y = fromInteger ((toInteger x `Bits.shiftR` NR.widthVal i) Bits..&. NR.maxUnsigned n) in
      member d x ==> property (member (select i n w d) y)

-- ------------------------------------------------------------------
-- ** Shifts and rotations

correct_shl ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shl w a x b y =
  member a x ==> member b y ==> property (member (shl w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toInteger x `Bits.shiftL` s)

correct_lshr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_lshr w a x b y =
  member a x ==> member b y ==> property (member (lshr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = fromInteger (toInteger x `Bits.shiftR` s)

correct_ashr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ashr w a x b y =
  member a x ==> member b y ==> property (member (ashr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toSigned w (toInteger x) `Bits.shiftR` s)

correct_rol ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_rol w a x b y =
  member a x ==> member b y ==>
    property (member (rol w a b) (fromInteger (Arith.rotateLeft w (toInteger x) (toInteger y))))

correct_ror ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ror w a x b y =
  member a x ==> member b y ==>
    property (member (ror w a b) (fromInteger (Arith.rotateRight w (toInteger x) (toInteger y))))

-- ------------------------------------------------------------------
-- ** Lattice operations

-- | 'join' is sound: every element of @a@ or @b@ is also in @join a b@.
correct_join ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_join w a b x =
  (member a x || member b x) ==> property (member (join w a b) x)

-- | 'meet' is a sound /over/-approximation of intersection: if @x@ is in
-- both @a@ and @b@, then @x@ is in @meet a b@.
correct_meet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_meet w a b x =
  (member a x && member b x) ==> property (member (meet w a b) x)

joinCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
joinCommutative w a b x =
  property (member (join w a b) x == member (join w b a) x)

joinIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
joinIdempotent w a x =
  member a x ==> property (member (join w a a) x)

joinTop ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
joinTop w a x =
  member a x ==> property (member (join w a (top w)) x)

joinBottom ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
joinBottom w a x =
  property (member (join w a (bottom w)) x == member a x)

meetCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
meetCommutative w a b x =
  property (member (meet w a b) x == member (meet w b a) x)

meetIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
meetIdempotent w a x =
  member a x ==> property (member (meet w a a) x)

meetTop ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
meetTop w a x =
  member a x ==> property (member (meet w a (top w)) x)

meetBottom ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
meetBottom w a x =
  property (Prelude.not (member (meet w a (bottom w)) x))

-- ------------------------------------------------------------------
-- ** Helpers

-- | Reduce an 'Integer' modulo @2^w@ and return it as a 'Natural'.
asN :: NatRepr w -> Integer -> Natural
asN w x = fromInteger (x Bits..&. NR.maxUnsigned w)

-- | Interpret the unsigned representation @x@ at width @w@ as a signed
-- 'Integer'.
toSigned :: (1 <= w) => NatRepr w -> Integer -> Integer
toSigned w x =
  if x' Bits..&. signBit == 0 then x' else x' - (signBit `Bits.shiftL` 1)
  where
    x' = x Bits..&. NR.maxUnsigned w
    signBit = 1 `Bits.shiftL` (NR.widthVal w - 1)

