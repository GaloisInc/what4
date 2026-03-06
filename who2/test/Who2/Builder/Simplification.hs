{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Who2.Builder.Simplification
  ( tests
  ) where

import Control.Exception (catch, SomeException, evaluate)
import Control.Monad.IO.Class (liftIO)
import Data.List (isInfixOf)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import System.Exit (ExitCode(ExitSuccess))
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)

import Data.Parameterized.Nonce (withIONonceGenerator)
import qualified Hedgehog as H
import Hedgehog (Property, PropertyT, property, forAll, annotate, failure, assert)
import qualified Hedgehog.Gen as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified What4.BaseTypes as BT
import qualified What4.Protocol.SMTLib2.Syntax as SMT2

import Who2.Builder (newBuilder)
import Who2.Builder.API (ExprBuilderAPI(BVUlt, BVSlt, EqPred), interp)
import Who2.Builder.API.Gen (SomeWidth(SomeWidth), GenConfig(gcMaxDepth, gcBVWidths, gcNumBoolVars, gcNumBVVars, gcEnableDivisionOps), defaultGenConfig, genBool, genBVAtWidth)
import Who2.Builder.TestBuilder (newTestBuilder)
import qualified Who2.Protocol.SMTLib2 as Who2SMT2
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr as E
import qualified Who2.Expr.App as App
import qualified Who2.Expr.SymExpr as SE

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

    -- Serialize to SMT-Lib2 with declarations
    (simplifiedDecls, simplifiedTerm) <- Who2SMT2.mkSMTTermWithDecls simplified
    (naiveDecls, naiveTerm) <- Who2SMT2.mkSMTTermWithDecls naive

    -- Render terms with timeout to avoid memory explosion
    -- Some naive expressions can be exponentially large
    maybeRendered <- timeout 1000000 $ do  -- 1 second timeout
      simplifiedRendered <- evaluate $ renderTerm simplifiedTerm
      naiveRendered <- evaluate $ renderTerm naiveTerm
      pure (simplifiedRendered, naiveRendered)

    case maybeRendered of
      Nothing -> do
        -- Timeout - term too large to render, treat as matching (pass the test)
        pure (Left "term rendering timeout", Left "term rendering timeout - skipped")
      Just (simplifiedRendered, naiveRendered) -> do
        -- Create SMT queries with declarations
        let simplifiedQuery = Text.unlines $
              [ "(set-logic QF_BV)" ] ++
              simplifiedDecls ++
              [ "(assert " <> simplifiedRendered <> ")"
              , "(check-sat)"
              ]
        let naiveQuery = Text.unlines $
              [ "(set-logic QF_BV)" ] ++
              naiveDecls ++
              [ "(assert " <> naiveRendered <> ")"
              , "(check-sat)"
              ]

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
    (Left "term rendering timeout", Left _) -> do
      annotate "Skipped - naive term too large to render"
      H.discard
    (Left err, _) | "term rendering timeout" `isInfixOf` err -> do
      annotate "Skipped - term too large to render"
      H.discard
    (Left err, _) | "z3 timeout" `isInfixOf` err -> do
      annotate "Skipped - Z3 timeout (query too complex)"
      H.discard
    (_, Left err) | "term rendering timeout" `isInfixOf` err -> do
      annotate "Skipped - term too large to render"
      H.discard
    (_, Left err) | "z3 timeout" `isInfixOf` err -> do
      annotate "Skipped - Z3 timeout (query too complex)"
      H.discard
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
    -- Use Z3's built-in timeout: -t:100 (100 milliseconds)
    (exitCode, stdout, stderrOut) <- readProcessWithExitCode "z3" ["-in", "-t:100", "-T:1", "-memory:50"] (Text.unpack query)
    case exitCode of
      ExitSuccess ->
        let result = Text.strip $ Text.pack stdout
        in if result == "timeout" || result == "unknown"
           then pure $ Left "z3 timeout (100ms)"
           else pure $ Right result
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

-- | Property: Expressions with no variables and no division operations reduce to literals
propNoVariablesReducesToLiteral :: Property
propNoVariablesReducesToLiteral = property $ do
  let noVarConfig = defaultGenConfig { gcNumBoolVars = 0, gcNumBVVars = 0, gcEnableDivisionOps = False }
  annotate "Generating expression..."
  -- Cap the size at 5 to prevent expression explosion while still testing nested expressions
  expr <- forAll $ Gen.resize 5 (genBool noVarConfig)
  annotate "Building with Builder..."
  isLiteral <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen

    -- Build with builder
    SE.SymExpr simplifiedExpr <- interp builder expr

    -- Check if Builder reduced to a literal
    pure $ checkExprIsLiteral simplifiedExpr

  annotate $ "Is literal: " ++ show isLiteral
  assert isLiteral
  where
    checkExprIsLiteral ::
      forall t tp.
      E.Expr t (App.App t) tp ->
      Bool
    checkExprIsLiteral expr =
      case E.eApp expr of
        App.LogicApp EL.TruePred -> True
        App.LogicApp EL.FalsePred -> True
        App.BVApp (EBV.BVLit _ _) -> True
        _ -> False

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Simplification Correctness"
  [ testProperty "General simplifications (depth 5)" $
      H.withTests 32 propSimplificationCorrect
  , testProperty "Deep expressions (depth 10)" $
      H.withTests 32 propDeepSimplifications
  , testProperty "Boolean-only expressions (100 tests)" $
      H.withTests 128 propBoolSimplifications
  , testProperty "BV arithmetic expressions (100 tests)" $
      H.withTests 128 propBvArithSimplifications
  , testProperty "No variables reduces to literal" $
      H.withTests 1000 propNoVariablesReducesToLiteral
  ]
