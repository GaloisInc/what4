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

module What4.Domains.BV.StridedInterval
  ( Domain
  -- * Construction
  , mk
  -- , singleton
  -- , fromRange
  -- , fromFoldable
  -- * Conversion
  -- , toArith
  -- , fromArith
  -- , toBitwise
  -- , fromBitwise
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
  -- , correct_toArith
  -- , correct_fromArith
  -- , roundtripArith
  -- , correct_toBitwise
  -- , correct_fromBitwise
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
import           GHC.TypeNats (Nat)
import           Numeric.Natural (Natural)

import           Data.Parameterized.NatRepr (NatRepr, maxUnsigned)
import qualified What4.Domains.BV.CLP as CLP
import           What4.Domains.BV.CLP (Clp)
import           What4.Domains.Verification (Property, property, Gen, chooseBool)

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
