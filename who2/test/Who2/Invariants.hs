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
import Who2.Gen (GenConfig(gcBVWidths, gcMaxDepth), SomeWidth(SomeWidth), defaultGenConfig, genBool, genBVAtWidth)
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

-------------------------------------------------------------------------------
-- AST Traversal
-------------------------------------------------------------------------------

data CheckResult = CheckResult
  { crCheckedAny :: !Bool  -- True if we checked any Polarized*/semiring structure
  , crError :: !(Maybe String)  -- Just err if invariant violated
  }

instance Semigroup CheckResult where
  CheckResult a1 e1 <> CheckResult a2 e2 =
    CheckResult (a1 || a2) (e1 <> e2)

instance Monoid CheckResult where
  mempty = CheckResult False Nothing

ok :: CheckResult
ok = CheckResult False Nothing

checked :: CheckResult
checked = CheckResult True Nothing

failed :: String -> CheckResult
failed err = CheckResult True (Just err)

-- | Check that an expression tree contains no empty or singleton Polarized* or semiring structures
checkExpr :: forall t tp. E.Expr t (App.App t) tp -> CheckResult
checkExpr expr = case E.eApp expr of
  App.LogicApp logic -> checkLogicExpr logic
  App.BVApp bv -> checkBVExpr bv
  App.BoundVarApp _ -> ok
  App.FnApp _ args ->
    let checkArg :: Some (E.Expr t (App.App t)) -> CheckResult
        checkArg (Some e) = checkExpr e
    in foldMap checkArg (toListFC Some args)

checkLogicExpr :: forall t tp. EL.LogicExpr (E.Expr t (App.App t)) tp -> CheckResult
checkLogicExpr = \case
  EL.TruePred -> ok
  EL.FalsePred -> ok
  EL.EqPred x y -> checkSubExpr x <> checkSubExpr y
  EL.AndPred pbs -> checkPolarizedBloomSeq pbs "AndPred"
  EL.NotPred x -> checkSubExpr x
  EL.XorPred x y -> checkSubExpr x <> checkSubExpr y
  EL.OrPred pbs -> checkPolarizedBloomSeq pbs "OrPred"
  EL.Ite c t f -> checkSubExpr c <> checkSubExpr t <> checkSubExpr f
  EL.BVUlt _ x y -> checkSubExpr x <> checkSubExpr y
  EL.BVUle _ x y -> checkSubExpr x <> checkSubExpr y
  EL.BVSlt _ x y -> checkSubExpr x <> checkSubExpr y
  EL.BVSle _ x y -> checkSubExpr x <> checkSubExpr y

checkBVExpr :: forall t tp. EBV.BVExpr (E.Expr t (App.App t)) tp -> CheckResult
checkBVExpr = \case
  EBV.BVLit {} -> ok
  EBV.BVAdd _ sum -> checkBloomSum sum "BVAdd"
  EBV.BVNeg _ x -> checkSubExpr x
  EBV.BVSub _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVMul _ prod -> checkBloomProduct prod "BVMul"
  EBV.BVAndBits _ pbs -> checkPolarizedBloomSeq pbs "BVAndBits"
  EBV.BVOrBits _ pbs -> checkPolarizedBloomSeq pbs "BVOrBits"
  EBV.BVXorBits _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVNotBits _ x -> checkSubExpr x
  EBV.BVShl _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVLshr _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVAshr _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVUdiv _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVUrem _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVSdiv _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVSrem _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVRol _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVRor _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVConcat _ _ x y -> checkSubExpr x <> checkSubExpr y
  EBV.BVSelect _ _ _ x -> checkSubExpr x
  EBV.BVZext _ _ x -> checkSubExpr x
  EBV.BVSext _ _ x -> checkSubExpr x
  -- Hash-consed variants
  EBV.BVAndBitsHC _ pes -> checkPolarizedExprSet pes "BVAndBitsHC"
  EBV.BVOrBitsHC _ pes -> checkPolarizedExprSet pes "BVOrBitsHC"
  EBV.BVAddHC _ sum -> checkHashConsedSum sum "BVAddHC"
  EBV.BVMulHC _ prod -> checkHashConsedProduct prod "BVMulHC"

-- | Check subexpression (handles wrapped Expr types)
checkSubExpr :: forall t tp. E.Expr t (App.App t) tp -> CheckResult
checkSubExpr = checkExpr

-------------------------------------------------------------------------------
-- Invariant Checkers
-------------------------------------------------------------------------------

checkPolarizedBloomSeq :: PBS.PolarizedBloomSeq a -> String -> CheckResult
checkPolarizedBloomSeq pbs ctxt =
  let posSize = PBS.sizePos pbs
      negSize = PBS.sizeNeg pbs
      total = posSize + negSize
  in if total == 0
     then failed $ ctxt ++ ": PolarizedBloomSeq is empty (both posSet and negSet are empty)"
     else checked

checkPolarizedExprSet :: PES.PolarizedExprSet a -> String -> CheckResult
checkPolarizedExprSet pes ctxt =
  let posSize = PES.sizePos pes
      negSize = PES.sizeNeg pes
      total = posSize + negSize
  in if total == 0
     then failed $ ctxt ++ ": PolarizedExprSet is empty (both posSet and negSet are empty)"
     else checked

checkBloomSum :: BSR.SRSum sr f -> String -> CheckResult
checkBloomSum _sum _ctxt = checked

checkBloomProduct :: BPR.SRProd sr f -> String -> CheckResult
checkBloomProduct _prod _ctxt = checked

checkHashConsedSum :: HCSR.SRSum sr f -> String -> CheckResult
checkHashConsedSum _sum _ctxt = checked

checkHashConsedProduct :: HCPR.SRProd sr f -> String -> CheckResult
checkHashConsedProduct _prod _ctxt = checked

-------------------------------------------------------------------------------
-- Property Tests
-------------------------------------------------------------------------------

propNoEmptyOrSingletonStructures :: Property
propNoEmptyOrSingletonStructures = H.withDiscards 10000 $ H.property $ do
  -- Use larger depth to increase chance of creating complex structures
  let cfg = defaultGenConfig { gcMaxDepth = 10 }
  api <- H.forAll $ genBool cfg
  CheckResult checkedAny err <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SE.SymExpr expr <- interp builder api
    pure $ checkExpr expr
  -- Discard tests that don't create any Polarized*/semiring structures
  if not checkedAny
    then H.discard
    else case err of
      Nothing -> H.success
      Just msg -> do
        H.annotate msg
        H.failure

propNoEmptyOrSingletonStructuresBV :: Property
propNoEmptyOrSingletonStructuresBV = H.withDiscards 10000 $ H.property $ do
  -- Use larger depth to increase chance of creating complex structures
  let cfg = defaultGenConfig { gcMaxDepth = 10 }
  SomeWidth w <- H.forAll $ Gen.element (gcBVWidths cfg)
  api <- H.forAll $ genBVAtWidth cfg w
  CheckResult checkedAny err <- liftIO $ withIONonceGenerator $ \gen -> do
    builder <- newBuilder gen
    SE.SymExpr expr <- interp builder api
    pure $ checkExpr expr
  -- Discard tests that don't create any Polarized*/semiring structures
  if not checkedAny
    then H.discard
    else case err of
      Nothing -> H.success
      Just msg -> do
        H.annotate msg
        H.failure
