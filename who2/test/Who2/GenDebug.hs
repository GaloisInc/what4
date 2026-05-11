{-# LANGUAGE TypeApplications #-}

module Who2.GenDebug where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Data.Parameterized.NatRepr (knownNat)
import Who2.Gen
import Who2.ExprBuilderAPI (ExprBuilderAPI(..))

-- Simple test to see if generator works with 0 variables
testGen :: IO ()
testGen = do
  let noVarConfig = defaultGenConfig { gcNumBoolVars = 0, gcNumBVVars = 0, gcEnableDivisionOps = False }
  putStrLn "Generating 10 expressions with 0 variables..."

  -- Generate 10 expressions with small size
  let smallGen = Gen.sized $ \_ -> Gen.resize 3 (genBool noVarConfig)

  results <- Gen.sample smallGen
  putStrLn $ "Generated " ++ show (length results) ++ " expressions"
  mapM_ (putStrLn . ("  - " ++) . show) results
  putStrLn "Done!"
