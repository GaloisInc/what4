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

TODO: all operations via Arith (initially)
TODO: precision tests via enumeration
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
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
  , bottom
  -- , join
  -- , meet
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
  -- ** Lattice operations
  -- , correct_top
  -- , correct_bottom
  -- , correct_leq
  -- -- *** Ordering
  -- , leqReflexive
  -- , leqTransitive
  -- , leqIrreflexive
  -- -- *** Join
  -- , correct_join
  -- , joinCommutative
  -- , joinIdempotent
  -- , joinTop
  -- , joinBottom
  -- , joinMonotonic
  -- , joinLeq
  -- -- *** Meet
  -- , correct_meet
  -- , meetCommutative
  -- , meetIdempotent
  -- , meetTop
  -- , meetBottom
  -- , meetMonotonic
  -- , meetLeq
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.&.))
import           GHC.TypeNats (Nat, type (<=))
import           Numeric.Natural (Natural)

import           Data.Parameterized.NatRepr (NatRepr, maxUnsigned)
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
-- * Construction

-- | /O(1)/. The empty set at width @w@.
bottom :: NatRepr w -> Domain w
bottom w = BVDBot (fromInteger (maxUnsigned w))
{-# INLINE bottom #-}

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
memberBottom w x = property (not (member (bottom w) x))

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
    property (member (fromArith w a) (fromIntegral (x .&. maxUnsigned w)))

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
    property (member (fromBitwise w b) (fromIntegral (x .&. maxUnsigned w)))

