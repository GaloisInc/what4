{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module VerifyBindings where

import           Control.Applicative
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog.Alt
import qualified Test.Verification as V


verifyGenerators :: V.GenEnv Gen
verifyGenerators = V.GenEnv { V.genChooseBool = Gen.bool
                            , V.genChooseInteger = \r -> Gen.integral (uncurry Range.linear r)
                            , V.genChooseInt = \r -> Gen.int (uncurry Range.linear r)
                            , V.genGetSize = Gen.sized (\s -> return $ unSize s)
                            }


genTest :: String -> V.Gen V.Property -> TestTree
genTest nm p = testProperty nm $ property $ mkProp =<< (forAll $ V.toNativeProperty verifyGenerators p)
  where mkProp (V.BoolProperty b) = test $ assert b
        mkProp (V.AssumptionProp a) = if (V.preCondition a) then (mkProp $ V.assumedProp a) else discard


setTestOptions :: TestTree -> TestTree
setTestOptions =
  -- some tests discard a lot of values based on preconditions;
  -- this helps prevent those tests from failing for insufficent coverage
  localOption (HedgehogDiscardLimit (Just 500000)) .

  -- run at least 5000 tests
  adjustOption (\(HedgehogTestLimit x) -> HedgehogTestLimit (max 5000 <$> x <|> Just 5000))
