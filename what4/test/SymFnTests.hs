{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module SymFnTests where

import           Control.Monad.IO.Class ( MonadIO, liftIO )

import           Data.Parameterized.Classes ( ShowF(..) )
import           Data.Parameterized.Context ( pattern (:>), (!) )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Map.Ordered as OMap
import           Hedgehog
import qualified LibBF as BF

-- import qualified What4.Utils.Log as Log
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           SerializeTestUtils
import qualified What4.Expr.Builder as S
import           What4.BaseTypes
import qualified What4.Interface as WI -- ( getConfiguration )
-- import qualified What4.Serialize.Normalize as WN

import qualified What4.Serialize.Printer as WOUT
import qualified What4.Serialize.Parser as WIN
import qualified What4.Serialize.FastSExpr as WSF


import           Prelude


symFnTests :: [TestTree]
symFnTests = [
  testGroup "SymFns" (mconcat [
    testBasicArguments WIN.parseSExpr
    , testFunctionCalls WIN.parseSExpr
    , testExpressions WIN.parseSExpr
    , testBasicArguments WSF.parseSExpr
    , testFunctionCalls WSF.parseSExpr
    , testExpressions WSF.parseSExpr
    ])
  ]

data BuilderData t = NoBuilderData

floatSinglePrecision :: FloatPrecisionRepr Prec32
floatSinglePrecision = knownRepr

floatSingleType :: BaseTypeRepr (BaseFloatType Prec32)
floatSingleType = BaseFloatRepr floatSinglePrecision

testBasicArguments :: (T.Text -> Either String WIN.SExpr) -> [TestTree]
testBasicArguments parseSExpr =
    [ testProperty "same argument type" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr (Ctx.empty :> BaseIntegerRepr :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i1of2
          let i2 = bvs ! Ctx.i2of2
          WI.intAdd sym i1 i2
    , testProperty "different argument types" $
         withTests 1 $
         property $ mkEquivalenceTest parseSExpr (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i1of2
          let b1 = bvs ! Ctx.i2of2
          WI.baseTypeIte sym b1 i1 i1
    ]


testFunctionCalls :: (T.Text -> Either String WIN.SExpr) -> [TestTree]
testFunctionCalls parseSExpr =
    [ testProperty "no arguments" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr Ctx.empty $ \sym _ -> do
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") Ctx.empty BaseBoolRepr
          WI.applySymFn sym ufn Ctx.empty
    , testProperty "two inner arguments" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr Ctx.empty $ \sym _ -> do
          i1 <- WI.intLit sym 0
          let b1 = WI.truePred sym
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) BaseBoolRepr
          WI.applySymFn sym ufn (Ctx.empty :> i1 :> b1)
    , testProperty "argument passthrough" $
         withTests 1 $
        property $ mkEquivalenceTest parseSExpr (Ctx.empty :> BaseBoolRepr :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i2of2
          let b1 = bvs ! Ctx.i1of2
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) BaseBoolRepr
          WI.applySymFn sym ufn (Ctx.empty :> i1 :> b1)
    ]


testExpressions :: (T.Text -> Either String WIN.SExpr) -> [TestTree]
testExpressions parseSExpr =
    [ testProperty "negative ints" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr Ctx.empty $ \sym _ -> do
          WI.intLit sym (-1)
    , testProperty "float lit" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr Ctx.empty $ \sym _ -> do
          WI.floatLit sym floatSinglePrecision (BF.bfFromInt 100)
    , testProperty "simple struct" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr Ctx.empty $ \sym _ -> do
          i1 <- WI.intLit sym 0
          let b1 = WI.truePred sym
          WI.mkStruct sym (Ctx.empty :> i1 :> b1)
    , testProperty "struct field access" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr (Ctx.empty :> BaseStructRepr (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr)) $ \sym bvs -> do
          let struct = bvs ! Ctx.baseIndex
          i1 <- WI.structField sym struct Ctx.i1of2
          b1 <- WI.structField sym struct Ctx.i2of2
          WI.mkStruct sym (Ctx.empty :> b1 :> i1)
    --, testProperty "simple constant array" $
    --    property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
    --      i1 <- WI.intLit sym 1
    --      WI.constantArray sym (Ctx.empty :> BaseIntegerRepr) i1
    , testProperty "array update" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr (Ctx.empty :> BaseArrayRepr (Ctx.empty :> BaseIntegerRepr) BaseIntegerRepr) $ \sym bvs -> do
          i1 <- WI.intLit sym 1
          i2 <- WI.intLit sym 2
          let arr = bvs ! Ctx.baseIndex
          WI.arrayUpdate sym arr (Ctx.empty :> i1) i2
    , testProperty "integer to bitvector" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr (Ctx.empty :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.baseIndex
          WI.integerToBV sym i1 (WI.knownNat @32)
    , testProperty "float negate" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr (Ctx.empty :> floatSingleType ) $ \sym flts -> do
          let f1 = flts ! Ctx.baseIndex
          WI.floatNeg sym f1
    , testProperty "float abs" $
        withTests 1 $
        property $ mkEquivalenceTest parseSExpr (Ctx.empty :> floatSingleType ) $ \sym flts -> do
          let f1 = flts ! Ctx.baseIndex
          WI.floatAbs sym f1
    ]

mkEquivalenceTest :: forall m args ret
                   . ( MonadTest m
                     , MonadIO m
                     )
                  => (T.Text -> Either String WIN.SExpr)
                  -> Ctx.Assignment BaseTypeRepr args
                  -> (forall sym
                       . WI.IsSymExprBuilder sym
                      => sym
                      -> Ctx.Assignment (WI.SymExpr sym) args
                      -> IO (WI.SymExpr sym ret))
                  -> m ()
mkEquivalenceTest parseSExpr argTs getExpr = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ S.newExprBuilder S.FloatRealRepr NoBuilderData r
  liftIO $ S.startCaching sym
  bvs <- liftIO $ forFC argTs $ \repr -> do
    n <- freshNonce r
    let nm = "bv" ++ show (indexValue n)
    WI.freshBoundVar sym (WI.safeSymbol nm) repr
  e <- liftIO $ getExpr sym (fmapFC (WI.varExpr sym) bvs)
  go sym bvs e
  where
    go :: forall sym t flgs st .
          ( WI.IsSymExprBuilder sym
          , sym ~ S.ExprBuilder t st flgs
          , ShowF (WI.SymExpr sym)
          )
       => sym
       -> Ctx.Assignment (WI.BoundVar sym) args
       -> WI.SymExpr sym ret
       -> m ()
    go sym bvs expr = do
      fn1 <- liftIO $ WI.definedFn sym (WI.safeSymbol "fn") bvs expr WI.NeverUnfold
      let scfg = WOUT.Config { WOUT.cfgAllowFreeVars = True
                             , WOUT.cfgAllowFreeSymFns = True
                             }
          res = WOUT.serializeSymFnWithConfig scfg fn1
          fnText = WOUT.printSExpr mempty $ WOUT.resSExpr res
          fnMap = Map.fromList $ map (\(x,y)->(y,x)) $ OMap.assocs $ WOUT.resSymFnEnv res
          exprMap = Map.fromList $
                    map (\((Some bv),freshName) ->
                           (freshName, (Some (WI.varExpr sym bv))))
                    $ OMap.assocs
                    $ WOUT.resFreeVarEnv res
      -- lcfg <- liftIO $ Log.mkLogCfg "rndtrip"
      deser <- do
        dcfg <- return $ (WIN.defaultConfig sym)
                { WIN.cSymFnLookup = \nm ->
                    case Map.lookup nm fnMap of
                      Nothing -> return Nothing
                      Just (WOUT.SomeExprSymFn fn) -> return $ Just (WIN.SomeSymFn fn)
                , WIN.cExprLookup = \nm ->
                    case Map.lookup nm exprMap of
                      Nothing -> return Nothing
                      Just (Some x) -> return $ Just (Some x)
                }
        case parseSExpr fnText of
          Left errMsg -> return $ Left errMsg
          Right sexpr -> liftIO $ WIN.deserializeSymFnWithConfig sym dcfg sexpr
      case deser of
        Left err -> do
          debugOut $ "Unexpected deserialization error: " ++ err ++ "!\n S-expression:\n"
          debugOut $ (T.unpack fnText) ++ "\n"
          failure
        Right (WIN.SomeSymFn fn2) -> do
          fn1out <- liftIO $ WI.definedFn sym (WI.safeSymbol "fn") bvs expr WI.NeverUnfold
          symFnEqualityTest sym fn1out fn2

