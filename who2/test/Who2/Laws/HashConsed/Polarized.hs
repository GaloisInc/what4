module Who2.Laws.HashConsed.Polarized
  ( -- Basic properties
    propPolarizedExprSetHashConsistency
  ) where

import Control.Monad (when)
import Data.Hashable (Hashable(hashWithSalt), hash)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.HashConsed.Polarized as PES
import qualified Who2.Expr.HashConsed.Set as ES
import qualified Who2.Expr.Bloom.Polarized as PBS
import Who2.Expr (HasId(..))

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

-- Mock expression type with HasId instance
data MockExpr = MockExpr Int
  deriving (Eq, Ord, Show)

instance HasId MockExpr where
  getId (MockExpr i) = i

instance Hashable MockExpr where
  hashWithSalt s (MockExpr i) = s `hashWithSalt` i

instance PBS.Polarizable MockExpr where
  polarity (MockExpr x)
    | x < 0 = PBS.Negative (MockExpr (negate x))
    | otherwise = PBS.Positive (MockExpr x)

genPolarizedExprSet :: H.Gen (PES.PolarizedExprSet MockExpr)
genPolarizedExprSet = do
  posElems <- Gen.list (Range.linear 0 5) $ MockExpr <$> Gen.int (Range.linear 1 100)
  negElems <- Gen.list (Range.linear 0 5) $ MockExpr <$> Gen.int (Range.linear 1 100)
  let posSet = ES.fromList posElems
  let negSet = ES.fromList negElems
  pure $ PES.PolarizedExprSet posSet negSet

-------------------------------------------------------------------------------
-- Hash Properties
-------------------------------------------------------------------------------

-- | PolarizedExprSet should maintain hash consistency: equal sets have equal hashes
propPolarizedExprSetHashConsistency :: Property
propPolarizedExprSetHashConsistency = H.property $ do
  pes1 <- H.forAll genPolarizedExprSet
  pes2 <- H.forAll genPolarizedExprSet
  when (pes1 == pes2) $ do
    hash pes1 H.=== hash pes2
