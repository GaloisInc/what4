{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module VerifyBindings where

import           Test.Tasty
import           Test.Tasty.QuickCheck
import qualified Test.Verification as V


instance Testable V.Property where
  property = \case
    V.BoolProperty b -> property b
    V.AssumptionProp a -> (V.preCondition a) ==> (V.assumedProp a)

verifyGenerators :: V.GenEnv Gen
verifyGenerators = V.GenEnv { V.genChooseBool = elements [ True, False ]
                            , V.genChooseInteger = \r -> choose r
                            , V.genChooseInt = \r -> choose r
                            , V.genGetSize = getSize
                            }


genTest :: String -> V.Gen V.Property -> TestTree
genTest nm p = testProperty nm (property $ V.toNativeProperty verifyGenerators p)


setTestOptions :: TestTree -> TestTree
setTestOptions =
  -- some tests discard a lot of values based on preconditions;
  -- this helps prevent those tests from failing for insufficent coverage
  localOption (QuickCheckMaxRatio 1000) .

  -- run at least 5000 tests
  adjustOption (\(QuickCheckTests x) -> QuickCheckTests (max x 5000))
