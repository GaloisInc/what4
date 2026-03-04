{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.Builder.API.GenTests
  ( tests
  ) where

import Control.Monad (replicateM)
import qualified Data.Set as Set

import Data.Parameterized.Nonce (withIONonceGenerator)
import qualified Hedgehog.Gen as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool)

import Who2.Builder (newBuilder)
import Who2.Builder.API (interp)
import Who2.Builder.API.Gen (defaultGenConfig, gcEnableDivisionOps, genBool, genBVAtWidth, SomeWidth(SomeWidth), gcBVWidths)
import qualified Who2.Expr as E
import qualified Who2.Expr.App as App
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr.SymExpr as SE

-- | All App constructors
data AppConstructor
  = BoundVarAppCons
  | LogicAppCons LogicConstructor
  | BVAppCons BVConstructor
  | FnAppCons
  deriving (Eq, Ord, Show)

data LogicConstructor
  = TruePredCons
  | FalsePredCons
  | EqPredCons
  | AndPredCons
  | AndPredHCCons
  | NotPredCons
  | XorPredCons
  | OrPredCons
  | OrPredHCCons
  | IteCons
  | BVUltCons
  | BVUleCons
  | BVSltCons
  | BVSleCons
  deriving (Eq, Ord, Show)

data BVConstructor
  = BVLitCons
  | BVAddCons
  | BVNegCons
  | BVSubCons
  | BVMulCons
  | BVAndBitsCons
  | BVOrBitsCons
  | BVXorBitsCons
  | BVNotBitsCons
  | BVShlCons
  | BVLshrCons
  | BVAshrCons
  | BVUdivCons
  | BVUremCons
  | BVSdivCons
  | BVSremCons
  | BVRolCons
  | BVRorCons
  | BVConcatCons
  | BVSelectCons
  | BVZextCons
  | BVSextCons
  | BVAndBitsHCCons
  | BVOrBitsHCCons
  | BVAddHCCons
  | BVMulHCCons
  deriving (Eq, Ord, Show)

-- | Classify the top-level App constructor
classifyApp :: App.App t (E.Expr t (App.App t)) tp -> AppConstructor
classifyApp = \case
  App.BoundVarApp _ -> BoundVarAppCons
  App.LogicApp logic -> LogicAppCons (classifyLogic logic)
  App.BVApp bv -> BVAppCons (classifyBV bv)
  App.FnApp _ _ -> FnAppCons

classifyLogic :: EL.LogicExpr f tp -> LogicConstructor
classifyLogic = \case
  EL.TruePred -> TruePredCons
  EL.FalsePred -> FalsePredCons
  EL.EqPred _ _ -> EqPredCons
  EL.AndPred _ -> AndPredCons
  EL.AndPredHC _ -> AndPredHCCons
  EL.NotPred _ -> NotPredCons
  EL.XorPred _ _ -> XorPredCons
  EL.OrPred _ -> OrPredCons
  EL.OrPredHC _ -> OrPredHCCons
  EL.Ite _ _ _ -> IteCons
  EL.BVUlt _ _ _ -> BVUltCons
  EL.BVUle _ _ _ -> BVUleCons
  EL.BVSlt _ _ _ -> BVSltCons
  EL.BVSle _ _ _ -> BVSleCons

classifyBV :: EBV.BVExpr f tp -> BVConstructor
classifyBV = \case
  EBV.BVLit _ _ -> BVLitCons
  EBV.BVAdd _ _ -> BVAddCons
  EBV.BVNeg _ _ -> BVNegCons
  EBV.BVSub _ _ _ -> BVSubCons
  EBV.BVMul _ _ -> BVMulCons
  EBV.BVAndBits _ _ -> BVAndBitsCons
  EBV.BVOrBits _ _ -> BVOrBitsCons
  EBV.BVXorBits _ _ _ -> BVXorBitsCons
  EBV.BVNotBits _ _ -> BVNotBitsCons
  EBV.BVShl _ _ _ -> BVShlCons
  EBV.BVLshr _ _ _ -> BVLshrCons
  EBV.BVAshr _ _ _ -> BVAshrCons
  EBV.BVUdiv _ _ _ -> BVUdivCons
  EBV.BVUrem _ _ _ -> BVUremCons
  EBV.BVSdiv _ _ _ -> BVSdivCons
  EBV.BVSrem _ _ _ -> BVSremCons
  EBV.BVRol _ _ _ -> BVRolCons
  EBV.BVRor _ _ _ -> BVRorCons
  EBV.BVConcat _ _ _ _ -> BVConcatCons
  EBV.BVSelect _ _ _ _ -> BVSelectCons
  EBV.BVZext _ _ _ -> BVZextCons
  EBV.BVSext _ _ _ -> BVSextCons
  EBV.BVAndBitsHC _ _ -> BVAndBitsHCCons
  EBV.BVOrBitsHC _ _ -> BVOrBitsHCCons
  EBV.BVAddHC _ _ -> BVAddHCCons
  EBV.BVMulHC _ _ -> BVMulHCCons

-- | All expected logic constructors (excluding normalized-away ones)
-- Note: XorPred and OrPred are normalized to NotPred+AndPred
-- Note: BVUle and BVSle are normalized to BVUlt and BVSlt
expectedLogicConstructors :: Set.Set LogicConstructor
expectedLogicConstructors = Set.fromList
  [ TruePredCons
  , FalsePredCons
  , EqPredCons
  , AndPredCons
  , NotPredCons
  , IteCons
  , BVUltCons
  , BVSltCons
  ]

-- | All expected BV constructors (excluding normalized-away ones)
-- Note: BVNeg is normalized to ~x+1 (bitwise not plus one)
-- Note: HC variants may not appear depending on config flags
expectedBVConstructors :: Set.Set BVConstructor
expectedBVConstructors = Set.fromList
  [ BVLitCons
  , BVAddCons
  , BVSubCons
  , BVMulCons
  , BVAndBitsCons
  , BVOrBitsCons
  , BVXorBitsCons
  , BVNotBitsCons
  , BVShlCons
  , BVLshrCons
  , BVAshrCons
  , BVUdivCons
  , BVUremCons
  , BVSdivCons
  , BVSremCons
  , BVRolCons
  , BVRorCons
  , BVConcatCons
  , BVSelectCons
  , BVZextCons
  , BVSextCons
  ]

-- | Run generator N times and collect top-level constructors
testBoolCoverage :: IO ()
testBoolCoverage = do
  let cfg = defaultGenConfig
      numTests = 1024

  seen <- withIONonceGenerator $ \nonceGen -> do
    builder <- newBuilder nonceGen

    -- Generate many expressions and collect their top-level constructors
    results <- replicateM numTests $ do
      -- Use Hedgehog's Gen monad
      api <- Gen.sample (genBool cfg)
      SE.SymExpr expr <- interp builder api
      pure $ classifyApp (E.eApp expr)

    pure $ Set.fromList results

  -- Extract just the logic constructors
  let seenLogic = Set.fromList
        [ lc | LogicAppCons lc <- Set.toList seen ]

  let missing = Set.difference expectedLogicConstructors seenLogic

  assertBool
    ("Generator did not produce all boolean constructors within " ++ show numTests ++ " tests.\n"
     ++ "Missing: " ++ show (Set.toList missing) ++ "\n"
     ++ "Seen: " ++ show (Set.toList seenLogic))
    (Set.null missing)

-- | Run generator N times and collect top-level BV constructors
testBVCoverage :: IO ()
testBVCoverage = do
  let cfg = defaultGenConfig { gcEnableDivisionOps = True }
      numTests = 1024
      widths = gcBVWidths cfg

  seen <- withIONonceGenerator $ \nonceGen -> do
    builder <- newBuilder nonceGen

    -- Generate many expressions and collect their top-level constructors
    results <- replicateM numTests $ do
      -- Pick a random width and generate
      let idx = numTests `mod` length widths
      case widths !! idx of
        SomeWidth w -> do
          api <- Gen.sample (genBVAtWidth cfg w)
          SE.SymExpr expr <- interp builder api
          pure $ classifyApp (E.eApp expr)

    pure $ Set.fromList results

  -- Extract just the BV constructors
  let seenBV = Set.fromList
        [ bvc | BVAppCons bvc <- Set.toList seen ]

  let missing = Set.difference expectedBVConstructors seenBV

  assertBool
    ("Generator did not produce all BV constructors within " ++ show numTests ++ " tests.\n"
     ++ "Missing: " ++ show (Set.toList missing) ++ "\n"
     ++ "Seen: " ++ show (Set.toList seenBV))
    (Set.null missing)

tests :: TestTree
tests = testGroup "Generator Coverage"
  [ testCase "Generates all bool constructors" testBoolCoverage
  , testCase "Generates all BV constructors" testBVCoverage
  ]
