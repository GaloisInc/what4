{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.Invariants
  ( propNoEmptyOrSingletonStructures
  , propNoEmptyOrSingletonStructuresBV
  ) where

import Control.Monad.IO.Class (liftIO)

import Data.Parameterized.Nonce (withIONonceGenerator)
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.TraversableFC (toListFC)
import Hedgehog (Property)
import qualified Hedgehog as H

import Who2.Builder (newBuilder)
import Who2.Gen (SomeWidth(..), defaultGenConfig, genBool, genBVAtWidth, gcBVWidths)
import Who2.Properties (interp)
import qualified Hedgehog.Gen as Gen
import qualified Who2.Expr as E
import qualified Who2.Expr.App as App
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr.SymExpr as SE
import qualified Who2.Expr.Bloom.Polarized as PBS
import qualified Who2.Expr.HashConsed.Polarized as PES
import qualified Who2.Expr.Bloom.SemiRing.Sum as BSR
import qualified Who2.Expr.Bloom.SemiRing.Product as BPR
import qualified Who2.Expr.HashConsed.SemiRing.Sum as HCSR
import qualified Who2.Expr.HashConsed.SemiRing.Product as HCPR
import qualified Who2.Expr.Bloom.Map as BKv

-------------------------------------------------------------------------------
-- AST Traversal
-------------------------------------------------------------------------------

-- | Check that an expression tree contains no empty or singleton Polarized* or semiring structures
checkExpr :: forall t tp. E.Expr t (App.App t) tp -> Either String ()
checkExpr expr = case E.eApp expr of
  App.LogicApp logic -> checkLogicExpr logic
  App.BVApp bv -> checkBVExpr bv
  App.BoundVarApp _ -> Right ()
  App.FnApp _ args ->
    let checkArg :: Some (E.Expr t (App.App t)) -> Either String ()
        checkArg (Some e) = checkExpr e
    in mapM_ checkArg (toListFC Some args)

checkLogicExpr :: forall t tp. EL.LogicExpr (E.Expr t (App.App t)) tp -> Either String ()
checkLogicExpr = \case
  EL.TruePred -> Right ()
  EL.FalsePred -> Right ()
  EL.EqPred x y -> checkSubExpr x >> checkSubExpr y
  EL.AndPred pbs -> checkPolarizedBloomSeq pbs "AndPred"
  EL.NotPred x -> checkSubExpr x
  EL.XorPred x y -> checkSubExpr x >> checkSubExpr y
  EL.OrPred pbs -> checkPolarizedBloomSeq pbs "OrPred"
  EL.Ite c t f -> checkSubExpr c >> checkSubExpr t >> checkSubExpr f
  EL.BVUlt _ x y -> checkSubExpr x >> checkSubExpr y
  EL.BVUle _ x y -> checkSubExpr x >> checkSubExpr y
  EL.BVSlt _ x y -> checkSubExpr x >> checkSubExpr y
  EL.BVSle _ x y -> checkSubExpr x >> checkSubExpr y

checkBVExpr :: forall t tp. EBV.BVExpr (E.Expr t (App.App t)) tp -> Either String ()
checkBVExpr = \case
  EBV.BVLit {} -> Right ()
  EBV.BVAdd _ sum -> checkBloomSum sum "BVAdd"
  EBV.BVNeg _ x -> checkSubExpr x
  EBV.BVSub _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVMul _ prod -> checkBloomProduct prod "BVMul"
  EBV.BVAndBits _ pbs -> checkPolarizedBloomSeq pbs "BVAndBits"
  EBV.BVOrBits _ pbs -> checkPolarizedBloomSeq pbs "BVOrBits"
  EBV.BVXorBits _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVNotBits _ x -> checkSubExpr x
  EBV.BVShl _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVLshr _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVAshr _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVUdiv _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVUrem _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVSdiv _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVSrem _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVRol _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVRor _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVConcat _ _ x y -> checkSubExpr x >> checkSubExpr y
  EBV.BVSelect _ _ _ x -> checkSubExpr x
  EBV.BVZext _ _ x -> checkSubExpr x
  EBV.BVSext _ _ x -> checkSubExpr x
  -- Hash-consed variants
  EBV.BVAndBitsHC _ pes -> checkPolarizedExprSet pes "BVAndBitsHC"
  EBV.BVOrBitsHC _ pes -> checkPolarizedExprSet pes "BVOrBitsHC"
  EBV.BVAddHC _ sum -> checkHashConsedSum sum "BVAddHC"
  EBV.BVMulHC _ prod -> checkHashConsedProduct prod "BVMulHC"

-- | Check subexpression (handles wrapped Expr types)
checkSubExpr :: forall t tp. E.Expr t (App.App t) tp -> Either String ()
checkSubExpr = checkExpr

-------------------------------------------------------------------------------
-- Invariant Checkers
-------------------------------------------------------------------------------

checkPolarizedBloomSeq :: PBS.PolarizedBloomSeq a -> String -> Either String ()
checkPolarizedBloomSeq pbs ctxt = do
  let posSize = PBS.sizePos pbs
  let negSize = PBS.sizeNeg pbs
  let total = posSize + negSize
  when (total == 0) $
    Left $ ctxt ++ ": PolarizedBloomSeq is empty (both posSet and negSet are empty)"
  when (total == 1) $
    Left $ ctxt ++ ": PolarizedBloomSeq is singleton (exactly one element total)"
  Right ()

checkPolarizedExprSet :: PES.PolarizedExprSet a -> String -> Either String ()
checkPolarizedExprSet pes ctxt = do
  let posSize = PES.sizePos pes
  let negSize = PES.sizeNeg pes
  let total = posSize + negSize
  when (total == 0) $
    Left $ ctxt ++ ": PolarizedExprSet is empty (both posSet and negSet are empty)"
  when (total == 1) $
    Left $ ctxt ++ ": PolarizedExprSet is singleton (exactly one element total)"
  Right ()

checkBloomSum :: BSR.SRSum sr f -> String -> Either String ()
checkBloomSum sum ctxt = do
  let size = BKv.size (BSR.sumMap sum)
  when (size == 1) $
    Left $ ctxt ++ ": SRSum (Bloom) is singleton (exactly one term)"
  Right ()

checkBloomProduct :: BPR.SRProd sr f -> String -> Either String ()
checkBloomProduct prod ctxt = do
  let size = BKv.size (BPR.prodMap prod)
  when (size == 1) $
    Left $ ctxt ++ ": SRProd (Bloom) is singleton (exactly one term)"
  Right ()

checkHashConsedSum :: HCSR.SRSum sr f -> String -> Either String ()
checkHashConsedSum sum ctxt = do
  let size = length (HCSR.toTerms sum)
  when (size == 1) $
    Left $ ctxt ++ ": SRSum (HashConsed) is singleton (exactly one term)"
  Right ()

checkHashConsedProduct :: HCPR.SRProd sr f -> String -> Either String ()
checkHashConsedProduct prod ctxt = do
  let size = length (HCPR.toTerms prod)
  when (size == 1) $
    Left $ ctxt ++ ": SRProd (HashConsed) is singleton (exactly one term)"
  Right ()

when :: Bool -> Either String () -> Either String ()
when True action = action
when False _ = Right ()

-------------------------------------------------------------------------------
-- Property Tests
-------------------------------------------------------------------------------

propNoEmptyOrSingletonStructures :: Property
propNoEmptyOrSingletonStructures = H.property $ do
  api <- H.forAll $ genBool defaultGenConfig
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SE.SymExpr expr <- interp builder api
    pure $ checkExpr expr
  case result of
    Right () -> H.success
    Left err -> do
      H.annotate err
      H.failure

propNoEmptyOrSingletonStructuresBV :: Property
propNoEmptyOrSingletonStructuresBV = H.property $ do
  SomeWidth w <- H.forAll $ Gen.element (gcBVWidths defaultGenConfig)
  api <- H.forAll $ genBVAtWidth defaultGenConfig w
  result <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SE.SymExpr expr <- interp builder api
    pure $ checkExpr expr
  case result of
    Right () -> H.success
    Left err -> do
      H.annotate err
      H.failure
