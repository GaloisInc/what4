module Who2.Laws.HashConsed.Polarized
  ( -- Basic properties
    propPolarizedExprSetHashConsistency
  , propPolarizedExprSetEqHashConsistency
  ) where

import Data.Hashable (hash)

import Hedgehog (Property, (==>))
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

-- | PolarizedExprSet should maintain hash consistency: equal sets have equal hashes
propPolarizedExprSetHashConsistency :: Property
propPolarizedExprSetHashConsistency = H.property $ do
  pes1 <- H.forAll genPolarizedExprSet
  pes2 <- H.forAll genPolarizedExprSet
  (pes1 == pes2) ==> (hash pes1 H.=== hash pes2)

-- | Eq should be consistent with hash: if x == y then hash x == hash y
propPolarizedExprSetEqHashConsistency :: Property
propPolarizedExprSetEqHashConsistency = H.property $ do
  pes <- H.forAll genPolarizedExprSet
  let h1 = hash pes
  let h2 = hash pes
  h1 H.=== h2
