{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Who2.Laws.Expr (tests) where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)

import Data.Parameterized.Nonce (withIONonceGenerator)
import qualified Data.Parameterized.Classes as PC
import Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))
import Hedgehog (Property)
import qualified Hedgehog as H
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Who2.Builder (newBuilder)
import Who2.Expr (eHash)
import Who2.Expr.SymExpr (SymExpr(SymExpr))
import Who2.Builder.API (interp)
import Who2.Builder.API.Gen (defaultGenConfig, genBool)
import Who2.Laws.Helpers (checkOrdTransitivity, checkOrdFTransitivity, checkOrdAntisymmetry, checkOrdFAntisymmetry)

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
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    pure (testEquality x y, eHash x, eHash y)
  case result of
    (Just Refl, hx, hy) -> hx H.=== hy
    (Nothing, _, _) -> H.discard

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
    pure $ checkOrdFAntisymmetry (PC.compareF x y) (PC.compareF y x)
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
    pure $ checkOrdFTransitivity (PC.compareF x y) (PC.compareF y z) (PC.compareF x z)
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
      (Just Refl, PC.LTF) -> False
      (Just Refl, PC.GTF) -> False
      (Nothing, PC.EQF) -> False
  unless result H.failure

-------------------------------------------------------------------------------
-- Ord Properties (on underlying Expr, not SymExpr)
-------------------------------------------------------------------------------

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

propOrdAntisymmetric :: Property
propOrdAntisymmetric = H.property $ do
  expr1 <- H.forAll $ genBool defaultGenConfig
  expr2 <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SymExpr x <- interp builder expr1
    SymExpr y <- interp builder expr2
    pure $ checkOrdAntisymmetry (compare x y) (compare y x)
  unless result H.failure

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
    pure $ checkOrdTransitivity (compare x y) (compare y z) (compare x z)
  unless result H.failure

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
      (True, LT) -> False
      (True, GT) -> False
      (False, EQ) -> False
  unless result H.failure

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Expr Properties"
  [ testGroup "TestEquality Properties"
      [ testProperty "Reflexivity (testEquality x x == Just Refl)" propTestEqualityReflexive
      , testProperty "Symmetry (testEquality x y == testEquality y x)" propTestEqualitySymmetric
      , testProperty "Transitivity" propTestEqualityTransitive
      , testProperty "Hash consistency (equal implies same hash)" $
          H.withTests 100 $ H.withDiscards 10000 propTestEqualityHashConsistent
      ]
  , testGroup "OrdF Properties"
      [ testProperty "Reflexivity (compareF x x == EQF)" $
          H.withTests 1000 propOrdFReflexive
      , testProperty "Antisymmetry (compareF x y opposite of compareF y x)" $
          H.withTests 1000 propOrdFAntisymmetric
      , testProperty "Transitivity" $
          H.withTests 1000 propOrdFTransitive
      , testProperty "Consistency with TestEquality" $
          H.withTests 1000 propOrdFConsistentWithTestEquality
      ]
  , testGroup "Ord Properties"
      [ testProperty "Reflexivity" $
          H.withTests 1000 propOrdReflexive
      , testProperty "Antisymmetry" $
          H.withTests 1000 propOrdAntisymmetric
      , testProperty "Transitivity" $
          H.withTests 1000 propOrdTransitive
      , testProperty "Consistency with Eq" $
          H.withTests 1000 propOrdConsistentWithEq
      ]
  ]
