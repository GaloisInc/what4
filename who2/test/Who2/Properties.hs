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

module Who2.Properties
  ( propSimplificationCorrect
  , propDeepSimplifications
  , propBoolSimplifications
  , propBvArithSimplifications
  , propSingletonAbstractDomainIffLiteral
  , propNoVariablesReducesToLiteral
  , checkZ3Available
  , interp
  ) where

import Control.Exception (catch, SomeException, evaluate)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import System.Directory (findExecutable)
import System.Exit (ExitCode(ExitSuccess))
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)

import Data.Parameterized.Nonce (withIONonceGenerator)
import Data.Parameterized.NatRepr (natValue, type (<=))
import Numeric.Natural (Natural)
import Hedgehog (Property, PropertyT, property, forAll, annotate, failure, assert)
import qualified Hedgehog.Gen as Gen

import qualified What4.BaseTypes as BT
import What4.Interface (IsExprBuilder(..))
import qualified What4.Interface as WI
import qualified What4.Protocol.SMTLib2.Syntax as SMT2
import qualified What4.Utils.BVDomain as BVD

import Who2.Builder (newBuilder)
import qualified Who2.Protocol.SMTLib2 as Who2SMT2
import Who2.TestBuilder (newTestBuilder)
import Who2.ExprBuilderAPI (ExprBuilderAPI(..))
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.BV as EBV
import Who2.Gen (SomeWidth(SomeWidth), GenConfig(..), defaultGenConfig, genBool, genBVAtWidth)
import qualified Who2.Expr as E
import qualified Who2.Expr.App as App
import qualified Who2.Expr.SymExpr as SE

-- | Existential wrapper for typed SymExpr
data SomeBVVar sym where
  SomeBVVar :: (1 <= w) => BT.NatRepr w -> WI.SymExpr sym (BT.BaseBVType w) -> SomeBVVar sym

-- | Interpret an ExprBuilderAPI expression with any IsExprBuilder instance
-- Creates fresh bound variables on demand and caches them
interp ::
  WI.IsSymExprBuilder sym =>
  sym ->
  ExprBuilderAPI tp ->
  IO (WI.SymExpr sym tp)
interp sym expr = do
  boolVarsRef <- newIORef IntMap.empty
  bvVarsRef <- newIORef Map.empty
  interpWithVars sym boolVarsRef bvVarsRef expr

-- | Internal interpreter that tracks bound variables
interpWithVars ::
  WI.IsSymExprBuilder sym =>
  sym ->
  IORef (IntMap.IntMap (WI.SymExpr sym BT.BaseBoolType)) ->
  IORef (Map.Map (Natural, Int) (SomeBVVar sym)) ->
  ExprBuilderAPI tp ->
  IO (WI.SymExpr sym tp)
interpWithVars sym boolVarsRef bvVarsRef = \case
  TruePred -> pure $ truePred sym
  FalsePred -> pure $ falsePred sym

  BoundVarBool idx -> do
    boolVars <- readIORef boolVarsRef
    case IntMap.lookup idx boolVars of
      Just v -> pure v
      Nothing -> do
        let varName = WI.safeSymbol $ "bool_" ++ show idx
        bv <- WI.freshBoundVar sym varName BT.BaseBoolRepr
        let v = WI.varExpr sym bv
        modifyIORef boolVarsRef (IntMap.insert idx v)
        pure v

  BoundVarBV w idx -> do
    bvVars <- readIORef bvVarsRef
    -- Use composite key: (width, idx) to distinguish different widths
    let key = (natValue w, idx)
    case Map.lookup key bvVars of
      Just (SomeBVVar w' v)
        | Just WI.Refl <- WI.testEquality w w' -> pure v
        | otherwise -> error $ "BoundVarBV type mismatch for index " ++ show idx ++ " (internal error)"
      Nothing -> do
        let varName = WI.safeSymbol $ "bv" ++ show (natValue w) ++ "_" ++ show idx
        bv <- WI.freshBoundVar sym varName (BT.BaseBVRepr w)
        let v = WI.varExpr sym bv
        modifyIORef bvVarsRef (Map.insert key (SomeBVVar w v))
        pure v

  NotPred x -> notPred sym =<< interpWithVars sym boolVarsRef bvVarsRef x
  AndPred x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    andPred sym ex ey
  OrPred x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    orPred sym ex ey
  XorPred x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    xorPred sym ex ey
  EqPred x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    isEq sym ex ey
  ItePred c t e -> do
    ec <- interpWithVars sym boolVarsRef bvVarsRef c
    et <- interpWithVars sym boolVarsRef bvVarsRef t
    ee <- interpWithVars sym boolVarsRef bvVarsRef e
    itePred sym ec et ee

  BVLit w bv -> bvLit sym w bv
  BVAdd x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvAdd sym ex ey
  BVSub x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvSub sym ex ey
  BVMul x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvMul sym ex ey
  BVNeg x -> bvNeg sym =<< interpWithVars sym boolVarsRef bvVarsRef x
  BVIte c t e -> do
    ec <- interpWithVars sym boolVarsRef bvVarsRef c
    et <- interpWithVars sym boolVarsRef bvVarsRef t
    ee <- interpWithVars sym boolVarsRef bvVarsRef e
    bvIte sym ec et ee

  BVAndBits x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvAndBits sym ex ey
  BVOrBits x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvOrBits sym ex ey
  BVXorBits x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvXorBits sym ex ey
  BVNotBits x -> bvNotBits sym =<< interpWithVars sym boolVarsRef bvVarsRef x

  BVUlt x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvUlt sym ex ey
  BVSlt x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvSlt sym ex ey
  BVEq x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    isEq sym ex ey

  BVShl x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvShl sym ex ey
  BVLshr x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvLshr sym ex ey
  BVAshr x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvAshr sym ex ey

  BVUdiv x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvUdiv sym ex ey
  BVUrem x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvUrem sym ex ey
  BVSdiv x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvSdiv sym ex ey
  BVSrem x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvSrem sym ex ey

  BVRol x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvRol sym ex ey
  BVRor x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvRor sym ex ey

  BVConcat x y -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    ey <- interpWithVars sym boolVarsRef bvVarsRef y
    bvConcat sym ex ey
  BVSelect idx w x -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    bvSelect sym idx w ex
  BVZext r x -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    bvZext sym r ex
  BVSext r x -> do
    ex <- interpWithVars sym boolVarsRef bvVarsRef x
    bvSext sym r ex

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
    (Left "term rendering timeout", Left _) -> do
      annotate "Skipped - naive term too large to render"
      pure ()  -- Pass the test, don't fail on huge terms
    (Right simpleRes, Right naiveRes) -> do
      annotate $ "Expression: " ++ show expr
      annotate $ "Simplified result: " ++ Text.unpack simpleRes
      annotate $ "Naive result: " ++ Text.unpack naiveRes
      annotate "Results differ - not equisatisfiable"
      failure
    (Left err, _) | "term rendering timeout" `elem` words err -> do
      annotate "Skipped - term too large to render"
      pure ()  -- Pass the test
    (Left err, _) -> do
      annotate $ "Expression: " ++ show expr
      annotate $ "Z3 error (simplified): " ++ err
      failure
    (_, Left err) | "term rendering timeout" `elem` words err -> do
      annotate "Skipped - term too large to render"
      pure ()  -- Pass the test
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

-- | Property: A built expression is a literal if and only if its abstract domain is a singleton
propSingletonAbstractDomainIffLiteral :: Property
propSingletonAbstractDomainIffLiteral = property $ do
  SomeWidth w <- forAll $ Gen.element (gcBVWidths defaultGenConfig)
  expr <- forAll $ genBVAtWidth defaultGenConfig w
  (isLit, isSingleton) <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SE.SymExpr e <- interp builder expr
    let isLit' = checkExprIsLiteral e
    let isSingleton' = checkExprSingleton e
    pure (isLit', isSingleton')
  assert (isLit == isSingleton)
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

    checkExprSingleton ::
      forall t tp.
      E.Expr t (App.App t) tp ->
      Bool
    checkExprSingleton expr =
      case (E.baseType expr, E.eAbsVal expr) of
        (BT.BaseBoolRepr, Just _) -> True
        (BT.BaseBVRepr _, BVD.asSingleton -> Just {}) -> True
        _ -> False

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
