{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Instances
  ( -- TestEquality properties
    propTestEqualityReflexive
  , propTestEqualitySymmetric
  , propTestEqualityTransitive
  , propTestEqualityHashConsistent
  -- OrdF properties
  , propOrdFReflexive
  , propOrdFAntisymmetric
  , propOrdFTransitive
  , propOrdFConsistentWithTestEquality
  -- Ord properties (on Expr, not SymExpr)
  , propOrdReflexive
  , propOrdAntisymmetric
  , propOrdTransitive
  , propOrdConsistentWithEq
  -- BloomSeq eqBy properties
  , propBloomSeqEqByReflexive
  , propBloomSeqEqBySymmetric
  , propBloomSeqEqByTransitive
  -- BloomSeq ordBy properties
  , propBloomSeqOrdByReflexive
  , propBloomSeqOrdByAntisymmetric
  , propBloomSeqOrdByTransitive
  , propBloomSeqOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)

import Data.Parameterized.Nonce (withIONonceGenerator)
import qualified Data.Parameterized.Classes as PC
import Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))
import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Who2.Builder (newBuilder)
import Who2.Expr (eHash)
import qualified Who2.Expr.BloomSeq as BS
import Who2.Expr.SymExpr (SymExpr(SymExpr))
import Who2.Gen (defaultGenConfig, genBool)
import Who2.Properties (interp)

-------------------------------------------------------------------------------
-- TestEquality Properties
-------------------------------------------------------------------------------

propTestEqualityReflexive :: Property
propTestEqualityReflexive = H.property $ do
  expr <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    x <- interp builder expr
    pure $ testEquality x x
  case result of
    Just Refl -> pure ()
    Nothing -> H.failure

propTestEqualitySymmetric :: Property
propTestEqualitySymmetric = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    x <- interp builder expr1
    y <- interp builder expr2
    pure (testEquality x y, testEquality y x)
  case result of
    (Just Refl, Just Refl) -> pure ()
    (Nothing, Nothing) -> pure ()
    (Just Refl, Nothing) -> H.failure
    (Nothing, Just Refl) -> H.failure

propTestEqualityTransitive :: Property
propTestEqualityTransitive = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  expr3 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    x <- interp builder expr1
    y <- interp builder expr2
    z <- interp builder expr3
    pure (testEquality x y, testEquality y z, testEquality x z)
  case result of
    (Just Refl, Just Refl, Nothing) -> H.failure
    _ -> pure ()

propTestEqualityHashConsistent :: Property
propTestEqualityHashConsistent = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  (hx, hy) <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    case testEquality x y of
      Just Refl -> pure (eHash x, eHash y)
      Nothing -> pure (0, 0)
  hx H.=== hy

-------------------------------------------------------------------------------
-- OrdF Properties
-------------------------------------------------------------------------------

propOrdFReflexive :: Property
propOrdFReflexive = H.property $ do
  expr <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr
    pure $ case PC.compareF x x of
      PC.EQF -> True
      _ -> False
  unless result H.failure

propOrdFAntisymmetric :: Property
propOrdFAntisymmetric = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    pure $ case (PC.compareF x y, PC.compareF y x) of
      (PC.LTF, PC.GTF) -> True
      (PC.EQF, PC.EQF) -> True
      (PC.GTF, PC.LTF) -> True
      _ -> False
  unless result H.failure

propOrdFTransitive :: Property
propOrdFTransitive = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  expr3 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    SymExpr z <- interp builder expr3
    pure $ case (PC.compareF x y, PC.compareF y z, PC.compareF x z) of
      (PC.LTF, PC.LTF, PC.LTF) -> True
      (PC.LTF, PC.LTF, _) -> False
      (PC.LTF, PC.EQF, PC.LTF) -> True
      (PC.LTF, PC.EQF, _) -> False
      (PC.EQF, PC.LTF, PC.LTF) -> True
      (PC.EQF, PC.LTF, _) -> False
      (PC.GTF, PC.GTF, PC.GTF) -> True
      (PC.GTF, PC.GTF, _) -> False
      (PC.GTF, PC.EQF, PC.GTF) -> True
      (PC.GTF, PC.EQF, _) -> False
      (PC.EQF, PC.GTF, PC.GTF) -> True
      (PC.EQF, PC.GTF, _) -> False
      (PC.EQF, PC.EQF, PC.EQF) -> True
      (PC.EQF, PC.EQF, _) -> False
      (PC.LTF, PC.GTF, _) -> True
      (PC.GTF, PC.LTF, _) -> True
  unless result H.failure

propOrdFConsistentWithTestEquality :: Property
propOrdFConsistentWithTestEquality = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    pure $ case (testEquality x y, PC.compareF x y) of
      (Just Refl, PC.EQF) -> True
      (Nothing, PC.LTF) -> True
      (Nothing, PC.GTF) -> True
      _ -> False
  unless result H.failure

-------------------------------------------------------------------------------
-- Ord Properties (on underlying Expr, not SymExpr)
-------------------------------------------------------------------------------

-- | Ord should be reflexive: compare x x == EQ
propOrdReflexive :: Property
propOrdReflexive = H.property $ do
  expr <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr
    pure $ case compare x x of
      EQ -> True
      _ -> False
  unless result H.failure

-- | Ord should be antisymmetric: compare x y == EQ implies x == y
propOrdAntisymmetric :: Property
propOrdAntisymmetric = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    pure $ case (compare x y, x == y) of
      (EQ, True) -> True
      (LT, False) -> True
      (GT, False) -> True
      _ -> False
  unless result H.failure

-- | Ord should be transitive
propOrdTransitive :: Property
propOrdTransitive = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  expr3 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    SymExpr z <- interp builder expr3
    pure $ case (compare x y, compare y z, compare x z) of
      (LT, LT, LT) -> True
      (LT, LT, _) -> False
      (LT, EQ, LT) -> True
      (LT, EQ, _) -> False
      (EQ, LT, LT) -> True
      (EQ, LT, _) -> False
      (GT, GT, GT) -> True
      (GT, GT, _) -> False
      (GT, EQ, GT) -> True
      (GT, EQ, _) -> False
      (EQ, GT, GT) -> True
      (EQ, GT, _) -> False
      (EQ, EQ, EQ) -> True
      (EQ, EQ, _) -> False
      (LT, GT, _) -> True
      (GT, LT, _) -> True
  unless result H.failure

-- | Ord should be consistent with Eq: x == y iff compare x y == EQ
propOrdConsistentWithEq :: Property
propOrdConsistentWithEq = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    pure $ case (x == y, compare x y) of
      (True, EQ) -> True
      (False, LT) -> True
      (False, GT) -> True
      _ -> False
  unless result H.failure

-------------------------------------------------------------------------------
-- BloomSeq eqBy Properties
-------------------------------------------------------------------------------

-- | Generator for BloomSeq of Ints
genBloomSeqInt :: H.Gen (BS.BloomSeq Int)
genBloomSeqInt = do
  list <- Gen.list (Range.linear 0 10) (Gen.int (Range.linear 0 100))
  pure $ BS.fromList list

-- | BloomSeq eqBy should be reflexive: eqBy cmp x x == True
propBloomSeqEqByReflexive :: Property
propBloomSeqEqByReflexive = H.property $ do
  bs <- H.forAll genBloomSeqInt
  H.assert $ BS.eqBy (==) bs bs

-- | BloomSeq eqBy should be symmetric: eqBy cmp x y == eqBy cmp y x
propBloomSeqEqBySymmetric :: Property
propBloomSeqEqBySymmetric = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let eq1 = BS.eqBy (==) bs1 bs2
  let eq2 = BS.eqBy (==) bs2 bs1
  eq1 H.=== eq2

-- | BloomSeq eqBy should be transitive: if eqBy cmp x y and eqBy cmp y z then eqBy cmp x z
propBloomSeqEqByTransitive :: Property
propBloomSeqEqByTransitive = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  bs3 <- H.forAll genBloomSeqInt
  let eq12 = BS.eqBy (==) bs1 bs2
  let eq23 = BS.eqBy (==) bs2 bs3
  let eq13 = BS.eqBy (==) bs1 bs3
  -- If eq12 and eq23, then eq13 must hold
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- BloomSeq ordBy Properties
-------------------------------------------------------------------------------

-- | BloomSeq ordBy should be reflexive: ordBy cmp x x == EQ
propBloomSeqOrdByReflexive :: Property
propBloomSeqOrdByReflexive = H.property $ do
  bs <- H.forAll genBloomSeqInt
  BS.ordBy compare bs bs H.=== EQ

-- | BloomSeq ordBy should be antisymmetric: ordBy cmp x y is opposite of ordBy cmp y x
propBloomSeqOrdByAntisymmetric :: Property
propBloomSeqOrdByAntisymmetric = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let ord1 = BS.ordBy compare bs1 bs2
  let ord2 = BS.ordBy compare bs2 bs1
  let result = case (ord1, ord2) of
        (LT, GT) -> True
        (EQ, EQ) -> True
        (GT, LT) -> True
        _ -> False
  unless result H.failure

-- | BloomSeq ordBy should be transitive
propBloomSeqOrdByTransitive :: Property
propBloomSeqOrdByTransitive = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  bs3 <- H.forAll genBloomSeqInt
  let ord12 = BS.ordBy compare bs1 bs2
  let ord23 = BS.ordBy compare bs2 bs3
  let ord13 = BS.ordBy compare bs1 bs3
  let result = case (ord12, ord23, ord13) of
        (LT, LT, LT) -> True
        (LT, LT, _) -> False
        (LT, EQ, LT) -> True
        (LT, EQ, _) -> False
        (EQ, LT, LT) -> True
        (EQ, LT, _) -> False
        (GT, GT, GT) -> True
        (GT, GT, _) -> False
        (GT, EQ, GT) -> True
        (GT, EQ, _) -> False
        (EQ, GT, GT) -> True
        (EQ, GT, _) -> False
        (EQ, EQ, EQ) -> True
        (EQ, EQ, _) -> False
        (LT, GT, _) -> True
        (GT, LT, _) -> True
  unless result H.failure

-- | BloomSeq ordBy should be consistent with eqBy
propBloomSeqOrdByConsistentWithEqBy :: Property
propBloomSeqOrdByConsistentWithEqBy = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let eq = BS.eqBy (==) bs1 bs2
  let ord = BS.ordBy compare bs1 bs2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        _ -> False
  unless result H.failure
