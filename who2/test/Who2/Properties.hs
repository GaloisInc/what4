{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Who2.Properties
  ( propSimplificationCorrect
  , propDeepSimplifications
  , propBoolSimplifications
  , propBvArithSimplifications
  , checkZ3Available
  , interp
  ) where

import Control.Exception (catch, SomeException)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import System.Directory (findExecutable)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

import Data.Parameterized.Nonce (withIONonceGenerator)
import Hedgehog (Property, PropertyT, property, forAll, annotate, failure)
import qualified Hedgehog.Gen as Gen

import qualified What4.BaseTypes as BT
import What4.Interface (IsExprBuilder(..))
import qualified What4.Interface as WI
import qualified What4.Protocol.SMTLib2.Syntax as SMT2

import Who2.Builder (newBuilder)
import qualified Who2.Protocol.SMTLib2 as Who2SMT2
import Who2.TestBuilder (newTestBuilder)
import Who2.ExprBuilderAPI (ExprBuilderAPI(..))
import Who2.Gen (SomeWidth(SomeWidth), defaultGenConfig, gcMaxDepth, gcBVWidths, genBool, genBVAtWidth)

-- | Interpret an ExprBuilderAPI expression with any IsExprBuilder instance
interp ::
  IsExprBuilder sym =>
  sym ->
  ExprBuilderAPI tp ->
  IO (WI.SymExpr sym tp)
interp sym = \case
  TruePred -> pure $ truePred sym
  FalsePred -> pure $ falsePred sym
  NotPred x -> notPred sym =<< interp sym x
  AndPred x y -> do
    ex <- interp sym x
    ey <- interp sym y
    andPred sym ex ey
  OrPred x y -> do
    ex <- interp sym x
    ey <- interp sym y
    orPred sym ex ey
  XorPred x y -> do
    ex <- interp sym x
    ey <- interp sym y
    xorPred sym ex ey
  EqPred x y -> do
    ex <- interp sym x
    ey <- interp sym y
    isEq sym ex ey
  ItePred c t e -> do
    ec <- interp sym c
    et <- interp sym t
    ee <- interp sym e
    itePred sym ec et ee

  BVLit w bv -> bvLit sym w bv
  BVAdd x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvAdd sym ex ey
  BVSub x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvSub sym ex ey
  BVMul x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvMul sym ex ey
  BVNeg x -> bvNeg sym =<< interp sym x
  BVIte c t e -> do
    ec <- interp sym c
    et <- interp sym t
    ee <- interp sym e
    bvIte sym ec et ee

  BVAndBits x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvAndBits sym ex ey
  BVOrBits x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvOrBits sym ex ey
  BVXorBits x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvXorBits sym ex ey
  BVNotBits x -> bvNotBits sym =<< interp sym x

  BVUlt x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvUlt sym ex ey
  BVSlt x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvSlt sym ex ey
  BVEq x y -> do
    ex <- interp sym x
    ey <- interp sym y
    isEq sym ex ey

  BVShl x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvShl sym ex ey
  BVLshr x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvLshr sym ex ey
  BVAshr x y -> do
    ex <- interp sym x
    ey <- interp sym y
    bvAshr sym ex ey

-- | Check if Z3 is available
checkZ3Available :: IO Bool
checkZ3Available = do
  result <- findExecutable "z3"
  case result of
    Just _ -> pure True
    Nothing -> pure False

-- | Helper function to compare simplified and naive interpretations using Z3
-- Checks equisatisfiability: both should have the same SAT/UNSAT result
checkSimplificationPreserved ::
  ExprBuilderAPI BT.BaseBoolType ->
  PropertyT IO ()
checkSimplificationPreserved expr = do
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    -- Build with Who2 builders
    builder <- newBuilder gen
    testBuilder <- newTestBuilder gen
    simplified <- interp builder expr
    naive <- interp testBuilder expr

    -- Serialize to SMT-Lib2
    simplifiedTerm <- Who2SMT2.mkSMTTerm simplified
    naiveTerm <- Who2SMT2.mkSMTTerm naive

    -- Create SMT queries
    let mkQuery term = Text.unlines
          [ "(set-logic QF_BV)"
          , "(assert " <> renderTerm term <> ")"
          , "(check-sat)"
          ]
    let simplifiedQuery = mkQuery simplifiedTerm
    let naiveQuery = mkQuery naiveTerm

    -- Check both with Z3
    simplifiedResult <- runZ3WithQuery simplifiedQuery
    naiveResult <- runZ3WithQuery naiveQuery

    -- Compare results
    pure (simplifiedResult, naiveResult)

  case result of
    (Right simpleRes, Right naiveRes) | simpleRes == naiveRes ->
      pure ()  -- Equisatisfiable
    (Right simpleRes, Right naiveRes) -> do
      annotate $ "Expression: " ++ show expr
      annotate $ "Simplified result: " ++ Text.unpack simpleRes
      annotate $ "Naive result: " ++ Text.unpack naiveRes
      annotate "Results differ - not equisatisfiable"
      failure
    (Left err, _) -> do
      annotate $ "Expression: " ++ show expr
      annotate $ "Z3 error (simplified): " ++ err
      failure
    (_, Left err) -> do
      annotate $ "Expression: " ++ show expr
      annotate $ "Z3 error (naive): " ++ err
      failure

-- | Render a Term to Text
renderTerm :: SMT2.Term -> Text.Text
renderTerm term = Text.Lazy.toStrict $ Builder.toLazyText $ SMT2.renderTerm term

-- | Run Z3 with an in-memory query
runZ3WithQuery :: Text.Text -> IO (Either String Text.Text)
runZ3WithQuery query = catch
  (do
    (exitCode, stdout, stderrOut) <- readProcessWithExitCode "z3" ["-in"] (Text.unpack query)
    case exitCode of
      ExitSuccess ->
        let result = Text.strip $ Text.pack stdout
        in pure $ Right result
      _ -> pure $ Left $ "z3 exited with error: " ++ stderrOut
  )
  (\(e :: SomeException) -> pure $ Left $ "Exception running z3: " ++ show e)

-- | Main property: simplifications preserve semantics (boolean expressions only)
propSimplificationCorrect :: Property
propSimplificationCorrect = property $ do
  expr <- forAll $ genBool defaultGenConfig
  checkSimplificationPreserved expr

-- | Property for deeper boolean expressions
propDeepSimplifications :: Property
propDeepSimplifications = property $ do
  let deepConfig = defaultGenConfig { gcMaxDepth = 10 }
  expr <- forAll $ genBool deepConfig
  checkSimplificationPreserved expr

-- | Property for Boolean-only expressions
propBoolSimplifications :: Property
propBoolSimplifications = property $ do
  expr <- forAll $ genBool defaultGenConfig
  checkSimplificationPreserved expr

-- | Property for BV arithmetic expressions (generates boolean comparisons)
propBvArithSimplifications :: Property
propBvArithSimplifications = property $ do
  SomeWidth w <- forAll $ Gen.element (gcBVWidths defaultGenConfig)
  bvExpr1 <- forAll $ genBVAtWidth defaultGenConfig w
  bvExpr2 <- forAll $ genBVAtWidth defaultGenConfig w
  -- Turn BV expressions into a boolean by comparing them
  expr <- forAll $ Gen.element
    [ BVUlt bvExpr1 bvExpr2
    , BVSlt bvExpr1 bvExpr2
    , EqPred bvExpr1 bvExpr2
    ]
  checkSimplificationPreserved expr
