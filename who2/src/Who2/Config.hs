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
  , useHashConsedStructures
    -- * Bloom Filter and Hashing
  , bloomFilter
  , hashedSequence
  , fancyHash
    -- * SMT Solver Hints
  , emitAbstractDomainConstraintsForBoundVars
  , emitAbstractDomainConstraintsForAllBV
    -- * AST Normalizations
  , normalizeXor
  , normalizeOr
  , normalizeBVNeg
  , normalizeBVUle
  , normalizeBVSle
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

-- | Use hash-consed data structures (IntMap-based) instead of bloom-based structures.
--
-- When enabled, builder functions create HC constructors:
--
-- * 'BVAndBitsHC' (uses PolarizedExprSet) instead of 'BVAndBits' (uses PolarizedBloomSeq)
-- * 'BVOrBitsHC' (uses PolarizedExprSet) instead of 'BVOrBits' (uses PolarizedBloomSeq)
-- * 'BVAddHC' (uses SRSum from HashConsed) instead of 'BVAdd' (uses SRSum from SemiRing.Sum)
-- * 'BVMulHC' (uses SRProd from HashConsed) instead of 'BVMul' (uses SRProd from SemiRing.Product)
--
-- * 'True':  Use IntMap-based storage for O(log n) operations
-- * 'False': Use bloom filter-based storage (default)
--
-- Build flag: @-f[+\/-]use-hash-consed-structures@ (default: disabled)
--
-- REQUIRES: hashConsing = True (enforced by CPP check below)
useHashConsedStructures :: Bool
#if defined(HASH_CONSING) && defined(USE_HASH_CONSED_STRUCTURES)
useHashConsedStructures = True
#else
useHashConsedStructures = False
#endif
{-# INLINE useHashConsedStructures #-}

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

------------------------------------------------------------------------
-- AST Normalizations

-- | Controls whether XOR is normalized to NOT(EQ).
--
-- * 'True':  x ⊕ y = ¬(x = y), no XorPred constructor created.
-- * 'False': Creates XorPred constructor for direct solver emission.
--
-- Build flag: @-f[+\/-]normalize-xor@ (default: enabled)
normalizeXor :: Bool
#ifdef NORMALIZE_XOR
normalizeXor = True
#else
normalizeXor = False
#endif
{-# INLINE normalizeXor #-}

-- | Controls whether OR is normalized to NOT(AND(NOT, NOT)).
--
-- * 'True':  x ∨ y = ¬(¬x ∧ ¬y), no OrPred constructor created.
-- * 'False': Creates OrPred constructor with PolarizedBloomSeq optimization.
--
-- Build flag: @-f[+\/-]normalize-or@ (default: enabled)
normalizeOr :: Bool
#ifdef NORMALIZE_OR
normalizeOr = True
#else
normalizeOr = False
#endif
{-# INLINE normalizeOr #-}

-- | Controls whether bvneg is normalized to two's complement.
--
-- * 'True':  -(x) = ~x + 1, no BVNeg constructor created.
-- * 'False': Creates BVNeg constructor for direct solver emission.
--
-- Build flag: @-f[+\/-]normalize-bvneg@ (default: enabled)
normalizeBVNeg :: Bool
#ifdef NORMALIZE_BVNEG
normalizeBVNeg = True
#else
normalizeBVNeg = False
#endif
{-# INLINE normalizeBVNeg #-}

-- | Controls whether bvule is normalized to bvult + eq.
--
-- * 'True':  x ≤ y = (x < y) ∨ (x = y), no BVUle constructor created.
-- * 'False': Creates BVUle constructor for direct solver emission.
--
-- Build flag: @-f[+\/-]normalize-bvule@ (default: enabled)
normalizeBVUle :: Bool
#ifdef NORMALIZE_BVULE
normalizeBVUle = True
#else
normalizeBVUle = False
#endif
{-# INLINE normalizeBVUle #-}

-- | Controls whether bvsle is normalized to bvslt + eq.
--
-- * 'True':  x ≤ₛ y = (x <ₛ y) ∨ (x = y), no BVSle constructor created.
-- * 'False': Creates BVSle constructor for direct solver emission.
--
-- Build flag: @-f[+\/-]normalize-bvsle@ (default: enabled)
normalizeBVSle :: Bool
#ifdef NORMALIZE_BVSLE
normalizeBVSle = True
#else
normalizeBVSle = False
#endif
{-# INLINE normalizeBVSle #-}
