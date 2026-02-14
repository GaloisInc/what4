module Who2.Laws.HashConsed.Polarized
  ( -- Basic properties
    propPolarizedExprSetEqHashConsistency
  ) where

import Control.Monad (unless)
import Data.Hashable (hash)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.HashConsed.Polarized as PES
import qualified Who2.Expr.HashConsed.Set as ES
import Who2.Laws.Helpers (MockExpr(..))

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

-- | PolarizedExprSet Eq/Hashable consistency: equal sets have equal hashes
propPolarizedExprSetEqHashConsistency :: Property
propPolarizedExprSetEqHashConsistency = H.property $ do
  pes1 <- H.forAll genPolarizedExprSet
  pes2 <- H.forAll genPolarizedExprSet
  unless (pes1 == pes2) H.discard
  hash pes1 H.=== hash pes2
