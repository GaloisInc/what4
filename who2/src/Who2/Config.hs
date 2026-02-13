{-# LANGUAGE CPP #-}

-- | Centralized configuration for Who2 expression builder.
--
-- This module collects all top-level 'Bool' configuration constants that
-- control performance and behavior features. Each constant can be controlled at
-- build time using Cabal flags.
--
-- To enable/disable features at build time:
-- @
-- cabal build -f+hash-consing          # Enable hash-consing (default: enabled)
-- cabal build -f-bloom-filter          # Disable bloom filtering
-- cabal build -f+fancy-hash            # Enable polynomial rolling hash
-- @
--
-- All constants use @INLINE@ pragmas for zero-overhead abstraction - when
-- disabled, the compiler eliminates dead code paths entirely.
module Who2.Config
  ( -- * Core Expression Features
    hashConsing
    -- * Bloom Filter and Hashing
  , bloomFilter
  , hashedSequence
  , fancyHash
    -- * SMT Solver Hints
  , emitAbstractDomainConstraintsForBoundVars
  , emitAbstractDomainConstraintsForAllBV
  ) where

------------------------------------------------------------------------
-- Core Expression Features

-- | Controls whether hash-consing (structural sharing) is enabled.
--
-- * 'True':  Builder maintains term cache for structural sharing.
--            Expressions are deduplicated, equality becomes nonce comparison.
-- * 'False': No caching, fresh terms always created (simpler, no cache overhead).
--
-- Build flag: @-f[+\/-]hash-consing@ (default: enabled)
--
-- Tests are expected to pass in both configurations.
hashConsing :: Bool
#ifdef HASH_CONSING
hashConsing = True
#else
hashConsing = False
#endif
{-# INLINE hashConsing #-}

------------------------------------------------------------------------
-- Bloom Filter and Hashing

-- | Controls whether bloom filtering is enabled for fast negative membership tests.
--
-- * 'True':  Use 64-bit bloom filter for O(1) negative lookups in BloomSeq.
--            If element hash not in filter, element definitely not present.
-- * 'False': Fall back to linear search (slower for larger sequences).
--
-- Build flag: @-f[+\/-]bloom-filter@ (default: enabled)
--
-- Related: Combined with BloomSeq.threshold (12) to disable filter for large sequences.
bloomFilter :: Bool
#ifdef BLOOM_FILTER
bloomFilter = True
#else
bloomFilter = False
#endif
{-# INLINE bloomFilter #-}

-- | Controls whether hash precomputation is enabled for HashedSequence.
--
-- * 'True':  Precompute and maintain hash in O(1) field for constant-time hashing.
-- * 'False': Set hash to 0, compute on-demand (trades time for space).
--
-- Build flag: @-f[+\/-]hashed-sequence@ (default: enabled)
--
-- Tests are expected to pass regardless of this setting.
hashedSequence :: Bool
#ifdef HASHED_SEQUENCE
hashedSequence = True
#else
hashedSequence = False
#endif
{-# INLINE hashedSequence #-}

-- | Controls which hashing strategy to use for HashedSequence.
--
-- * 'True':  Polynomial rolling hash (order-sensitive, good distribution, base=31).
-- * 'False': Simple XOR (order-insensitive, risk of hash cancellation).
--
-- Build flag: @-f[+\/-]fancy-hash@ (default: disabled)
--
-- Only matters when hashedSequence = True.
fancyHash :: Bool
#ifdef FANCY_HASH
fancyHash = True
#else
fancyHash = False
#endif
{-# INLINE fancyHash #-}

------------------------------------------------------------------------
-- SMT Solver Hints

-- | Controls whether abstract domain constraints are emitted for bound variables.
--
-- * 'True':  Bound variables wrapped with @bvand@\/@bvor@ to encode known bits.
--            Provides solver hints with minimal cost (linear in #variables).
-- * 'False': No additional constraints (cleaner SMT output).
--
-- Build flag: @-f[+\/-]emit-ad-constraints-bound-vars@ (default: disabled)
emitAbstractDomainConstraintsForBoundVars :: Bool
#ifdef EMIT_AD_CONSTRAINTS_BOUND_VARS
emitAbstractDomainConstraintsForBoundVars = True
#else
emitAbstractDomainConstraintsForBoundVars = False
#endif
{-# INLINE emitAbstractDomainConstraintsForBoundVars #-}

-- | Controls whether abstract domain constraints are emitted for ALL bitvector expressions.
--
-- * 'True':  ALL BV expressions wrapped with @bvand@\/@bvor@ to encode known bits.
--            WARNING: Potentially very expensive, needs more benchmarking.
-- * 'False': No additional constraints (standard behavior).
--
-- Build flag: @-f[+\/-]emit-ad-constraints-all-bv@ (default: disabled)
emitAbstractDomainConstraintsForAllBV :: Bool
#ifdef EMIT_AD_CONSTRAINTS_ALL_BV
emitAbstractDomainConstraintsForAllBV = True
#else
emitAbstractDomainConstraintsForAllBV = False
#endif
{-# INLINE emitAbstractDomainConstraintsForAllBV #-}
