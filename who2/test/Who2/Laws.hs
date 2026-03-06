-- | Property tests for algebraic laws of Who2 data structures.
--
-- Tests verify that Eq, Ord, Hashable, and other typeclass instances
-- satisfy their required laws. Matched by @-- test-law:@ comments,
-- see "Who2.TestAnnotations" for details.
module Who2.Laws (tests) where

import Test.Tasty (TestTree, testGroup)

import qualified Who2.Laws.Bloom.HashedSeq as LawsBloomHashedSeq
import qualified Who2.Laws.Bloom.Map as LawsBloomMap
import qualified Who2.Laws.Bloom.Polarized as LawsBloomPolarized
import qualified Who2.Laws.Bloom.SemiRing.Product as LawsBloomProduct
import qualified Who2.Laws.Bloom.SemiRing.Sum as LawsBloomSum
import qualified Who2.Laws.Bloom.Set as LawsBloomSet
import qualified Who2.Laws.Expr as LawsExpr
import qualified Who2.Laws.HashConsed.Map as LawsHashConsedMap
import qualified Who2.Laws.HashConsed.Polarized as LawsHashConsedPolarized
import qualified Who2.Laws.HashConsed.SemiRing.Product as LawsHashConsedProduct
import qualified Who2.Laws.HashConsed.SemiRing.Sum as LawsHashConsedSum
import qualified Who2.Laws.HashConsed.Set as LawsHashConsedSet

tests :: TestTree
tests = testGroup "Laws"
  [ LawsExpr.tests
  , testGroup "Bloom Module Laws"
      [ LawsBloomSet.tests
      , LawsBloomMap.tests
      , LawsBloomPolarized.tests
      , LawsBloomHashedSeq.tests
      , LawsBloomSum.tests
      , LawsBloomProduct.tests
      ]
  , testGroup "HashConsed Module Laws"
      [ LawsHashConsedSet.tests
      , LawsHashConsedMap.tests
      , LawsHashConsedPolarized.tests
      , LawsHashConsedSum.tests
      , LawsHashConsedProduct.tests
      ]
  ]
