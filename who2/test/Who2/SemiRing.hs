module Who2.SemiRing (tests) where

import Test.Tasty (TestTree, testGroup)

import qualified Who2.SemiRing.Bloom.Product as BloomProduct
import qualified Who2.SemiRing.Bloom.Sum as BloomSum
import qualified Who2.SemiRing.HashConsed.Product as HashConsedProduct
import qualified Who2.SemiRing.HashConsed.Sum as HashConsedSum

tests :: TestTree
tests = testGroup "SemiRing Algebraic Laws"
  [ HashConsedSum.tests
  , HashConsedProduct.tests
  , BloomSum.tests
  , BloomProduct.tests
  ]
