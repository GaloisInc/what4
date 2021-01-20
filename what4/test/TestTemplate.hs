{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
--module TestTemplate where

module Main where

import Control.Monad ((<=<))
import Control.Monad.IO.Class (liftIO)
import Data.Bits
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Nonce
import Data.Parameterized.Pair
import Data.String

import LibBF
import qualified Data.BitVector.Sized as BV

import What4.BaseTypes
import What4.Interface

import           What4.Protocol.SMTWriter ((.==), mkSMTTerm)
import qualified What4.Protocol.SMTWriter as SMT
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Solver.Z3 as Z3
import           What4.Solver.Adapter (defaultLogData)

import What4.Expr.Builder
import What4.Expr.GroundEval
import What4.Utils.FloatHelpers

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Gen

data State t = State

main :: IO ()
main =
  do let xs = do r <- [RNE]
                 floatTemplates [r] 1 (knownRepr :: FloatPrecisionRepr Prec32)
     sym <- newExprBuilder FloatIEEERepr State globalNonceGenerator 
     _ <- checkSequential $ Group "Float tests"
       [ ( fromString (show t), templateGroundEvalTest sym t)
       | t <- xs
       ] 
     return ()

data FUnOp
  = FNeg
  | FAbs
  | FSqrt RoundingMode
  | FRound RoundingMode
 deriving (Show)

data FBinOp
  = FAdd RoundingMode
  | FSub RoundingMode
  | FMul RoundingMode
  | FDiv RoundingMode
  | FRem
  | FMin
  | FMax
 deriving (Show)

roundingModes :: [RoundingMode]
roundingModes = [ RNE, RNA, RTP, RTN, RTZ ]

fBinOps :: [RoundingMode] -> [FBinOp]
fBinOps rs =
  (FAdd <$> rs) <>
  (FSub <$> rs) <>
  (FMul <$> rs) <>
  (FDiv <$> rs) <>
  [ FRem, FMin, FMax ]

fUnOps :: [RoundingMode] -> [FUnOp]
fUnOps rs =
  [ FNeg, FAbs ] <>
  (FSqrt <$> rs) <>
  (FRound <$> rs)

-- | This datatype essentially mirrors the public API of the
--   What4 interface.  There should (eventually) be one element
--   of this datatype per syntax former method in "What4.Interface".
--   Each template represents a fragment of syntax that could be
--   generated.  We use these templates to test constant folding,
--   ground evaluation, term simplifications, fidelity
--   WRT solver term semantics and soundness of abstract domains.
--
--   The overall idea is that we want to enumerate all small
--   templates and use each template to generate a collection of test
--   cases.  Hopefully we can achieve high code path coverages with
--   a relatively small depth of templates, which should keep this process
--   managable.  We also have the option to manually generate templates
--   if necessary to increase test coverage.
data TestTemplate tp where
  TVar :: BaseTypeRepr tp -> TestTemplate tp

  TFloatPZero :: FloatPrecisionRepr fpp -> TestTemplate (BaseFloatType fpp)
  TFloatNZero :: FloatPrecisionRepr fpp -> TestTemplate (BaseFloatType fpp)
  TFloatNaN   :: FloatPrecisionRepr fpp -> TestTemplate (BaseFloatType fpp)

  TFloatUnOp ::
    FUnOp ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseFloatType fpp)

  TFloatBinOp ::
    FBinOp ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseFloatType fpp)

instance Show (TestTemplate tp) where
  showsPrec d tt = case tt of
    TVar{}        -> showString "_"
    TFloatPZero{} -> showString "+0.0"
    TFloatNZero{} -> showString "-0.0"
    TFloatNaN{}   -> showString "NaN"
    TFloatUnOp op x -> showParen (d > 0) $
       shows op . showString " " . showsPrec 10 x
    TFloatBinOp op x y -> showParen (d > 0) $
       shows op . showString " " . showsPrec 10 x . showString " " . showsPrec 10 y

templateDepth :: TestTemplate tp -> Integer
templateDepth = f
  where
  f :: TestTemplate tp -> Integer
  f t = case t of
          TVar{} -> 0

          TFloatPZero{} -> 0
          TFloatNZero{} -> 0
          TFloatNaN{}  -> 0

          TFloatUnOp _op x    -> 1 + (f x)
          TFloatBinOp _op x y -> 1 + max (f x) (f y)


floatOps ::
  [RoundingMode] ->
  [TestTemplate (BaseFloatType fpp)] ->
  [TestTemplate (BaseFloatType fpp)]
floatOps rs subterms = uops <> bops
  where
    uops = [ TFloatUnOp op x | op <- fUnOps rs, x <- subterms ]
    bops = [ TFloatBinOp op x y | op <- fBinOps rs, x <- subterms, y <- subterms ]

floatTemplates ::
  [RoundingMode] ->
  Integer ->
  FloatPrecisionRepr fpp ->
  [TestTemplate (BaseFloatType fpp)]
floatTemplates rs n fpp
  | n <= 0 = base
  | n == 1 = floatOps rs base
  | otherwise = f n

  where
   base = [ TVar (BaseFloatRepr fpp), TFloatPZero fpp, TFloatNZero fpp, TFloatNaN fpp ]

   f d | d < 1 = [ TVar (BaseFloatRepr fpp) ]
   f d = let xs = f (d-1) in xs <> floatOps rs xs


generateByType :: BaseTypeRepr tp -> Gen (GroundValue tp)
generateByType (BaseFloatRepr fpp) = genFloat fpp
generateByType tp = error ("generateByType! TODO " ++ show tp)

genFloat :: FloatPrecisionRepr fpp -> Gen BigFloat
genFloat (FloatingPointPrecisionRepr eb sb) =
    Gen.frequency
        [(1, pure bfPosZero)
        ,(1, pure bfNegZero)
        ,(1, pure bfPosInf)
        ,(1, pure bfNegInf)
        ,(1, pure bfNaN)
        ,(95, genNormal)
        ]
 where
  genNormal =
    do let emax = bit (fromInteger (intValue eb - 1)) - 1
       let smax = bit (fromInteger (intValue sb)) - 1
       let opts = fpOpts (intValue sb) (intValue sb) NearEven
       sgn <- Gen.bool
       ex  <- Gen.integral (Gen.linearFrom 0 (1-emax) emax)
       mag <- Gen.integral (Gen.linear 0 smax)
       let (x,Ok) = bfMul2Exp opts (bfFromInteger mag) ex
       pure $ (if sgn then bfNeg x else x)


mapGroundEval :: forall t. MapF (Expr t) GroundValueWrapper -> GroundEvalFn t
mapGroundEval m = GroundEvalFn f
  where
    f :: forall tp. Expr t tp -> IO (GroundValue tp)
    f x = case MapF.lookup x m of
            Just v -> pure (unGVW v)
            Nothing -> evalGroundExpr f x

solverEval :: forall t st fs tp.
  ExprBuilder t st fs -> MapF (Expr t) GroundValueWrapper -> Expr t tp -> IO (GroundValue tp)
solverEval sym gmap expr = Z3.withZ3 sym "z3" defaultLogData $ \s ->
  do let f :: Pair (Expr t) GroundValueWrapper -> IO SMT2.Term
         f (Pair e (GVW v)) =
            case exprType e of
              BaseFloatRepr fpp ->
                do e' <- mkSMTTerm (SMT2.sessionWriter s) e
                   return (e' .== SMT.floatTerm fpp v)
              tp -> fail ("solverEval: TODO " ++ show tp)

     mapM_ (SMT.assumeFormula (SMT2.sessionWriter s) <=< f) (MapF.toList gmap)

     e' <- mkSMTTerm (SMT2.sessionWriter s) expr
     SMT2.writeGetValue (SMT2.sessionWriter s) [e']
      
     case exprType expr of
       BaseFloatRepr fpp@(FloatingPointPrecisionRepr eb sb) ->
          do bv <- SMT.smtEvalFloat (SMT2.smtLibEvalFuns s) fpp e'
             return (floatFromBits (intValue eb) (intValue sb) (BV.asUnsigned bv))
       tp -> fail ("solverEval: TODO2 " ++ show tp)

showMap :: MapF (Expr t) GroundValueWrapper -> String
showMap gmap = unlines (map f (MapF.toList gmap))
  where
    f :: Pair (Expr t) (GroundValueWrapper) -> String
    f (Pair e (GVW v)) =
      case exprType e of
        BaseFloatRepr _ -> show (printSymExpr e) <> " " <> show v
        tp -> "showMap : TODO " <> show tp

templateGroundEvalTest ::
  ExprBuilder t st fs ->
  TestTemplate tp ->
  Property
templateGroundEvalTest sym t = property $
  do (gmapGen, expr) <- liftIO (templateGen sym t)
     annotateShow (printSymExpr expr)
     gmap <- forAllWith showMap gmapGen
     v  <- liftIO (groundEval (mapGroundEval gmap) expr)
     v' <- liftIO (solverEval sym gmap expr)
     Just True === groundEq (exprType expr) v v'

-- | Use the template to create an expression, and a Hedgehog generator that
--   builds a map from variables to concrete values for creating individual
--   test cases.
templateGen :: ExprBuilder t st fs -> TestTemplate tp -> IO (Gen (MapF (Expr t) GroundValueWrapper), Expr t tp)
templateGen sym = f
  where
    f (TVar bt) =
       do v <- freshConstant sym emptySymbol bt
          return (MapF.singleton v . GVW <$> generateByType bt, v)

    f (TFloatPZero fpp) =
       do e <- floatPZero sym fpp
          return (pure MapF.empty, e)

    f (TFloatNZero fpp) =
       do e <- floatNZero sym fpp
          return (pure MapF.empty, e)

    f (TFloatNaN fpp) =
        do e <- floatNaN sym fpp
           return (pure MapF.empty, e)

    f (TFloatUnOp op x) =
        do (xg,xe) <- f x
           e <- case op of
                  FNeg     -> floatNeg sym xe
                  FAbs     -> floatAbs sym xe
                  FSqrt  r -> floatSqrt sym r xe
                  FRound r -> floatRound sym r xe
           return (xg, e)

    f (TFloatBinOp op x y) =
        do (xg,xe) <- f x
           (yg,ye) <- f y
           e <- case op of
                  FAdd r -> floatAdd sym r xe ye
                  FSub r -> floatSub sym r xe ye
                  FMul r -> floatMul sym r xe ye
                  FDiv r -> floatDiv sym r xe ye
                  FRem   -> floatRem sym xe ye
                  FMin   -> floatMin sym xe ye
                  FMax   -> floatMax sym xe ye

           return (MapF.union <$> xg <*> yg, e)
