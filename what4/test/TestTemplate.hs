{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
--module TestTemplate where

module Main where

import Control.Exception
import Control.Monad ((<=<)) -- , when)
import Control.Monad.IO.Class (liftIO)
import           Control.Monad.Trans.Maybe
import Data.Bits
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Nonce
import Data.Parameterized.Pair
import Data.Parameterized.Some
import Data.String
import Numeric (showHex)
-- import System.IO

import LibBF
import qualified Data.BitVector.Sized as BV

import What4.BaseTypes
import What4.Config
import What4.Interface

import           What4.Protocol.SMTWriter ((.==), mkSMTTerm)
import qualified What4.Protocol.SMTWriter as SMT
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Protocol.Online as Online
import           What4.Protocol.Online (SolverProcess(..), OnlineSolver(..))
import qualified What4.Solver.CVC4 as CVC4

import What4.Expr
import What4.Expr.App (reduceApp)
import What4.Expr.Builder
import What4.Expr.GroundEval
import What4.SatResult

import What4.Utils.Arithmetic
import What4.Utils.FloatHelpers

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Gen
import GHC.Stack

--import Debug.Trace (trace)



main :: IO ()
main =
  do let fpp = knownRepr :: FloatPrecisionRepr Prec32

     let xs = castTemplates RNE <>
              (Some <$> floatTestTemplates [] 0 fpp) <>
              (do r <- roundingModes
                  (Some <$> floatTemplates [r] 1 fpp))

     sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState globalNonceGenerator

     extendConfig CVC4.cvc4Options (getConfiguration sym)
     proc <- Online.startSolverProcess @(SMT2.Writer CVC4.CVC4) CVC4.cvc4Features Nothing sym

     let testnum = 500

     tests <- sequence [ do p <- templateGroundEvalTestAlt sym proc t testnum
                            --p <- templateGroundEvalTest sym proc t testnum
                            --p <- templateConstantFoldTest sym t testnum
                            pure (fromString (show t), p)
                       | Some t <- xs
                       ]
     _ <- checkSequential $ Group "Float tests" tests
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

data FTestOp
  = FIsNaN
  | FIsInf
  | FIsZero
  | FIsPos
  | FIsNeg
  | FIsSubnorm
  | FIsNorm
 deriving Show

data FRelOp
  = FLogicEq
  | FLogicNeq
  | FEq
  | FApart
  | FUnordered
  | FLe
  | FLt
  | FGe
  | FGt
 deriving Show

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

  TFloatTest ::
    FTestOp ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate BaseBoolType

  TFloatRel ::
    FRelOp ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate BaseBoolType

  TFloatFromBits :: (2 <= eb, 2 <= sb) =>
    FloatPrecisionRepr (FloatingPointPrecision eb sb) ->
    TestTemplate (BaseBVType (eb + sb)) ->
    TestTemplate (BaseFloatType (FloatingPointPrecision eb sb))

  TFloatToBits :: (2 <= eb, 2 <= sb) =>
    TestTemplate (BaseFloatType (FloatingPointPrecision eb sb)) ->
    TestTemplate (BaseBVType (eb + sb))

  TBVToFloat :: (1 <= w) =>
    FloatPrecisionRepr fpp ->
    RoundingMode ->
    Bool {- False = unsigned -} ->
    TestTemplate (BaseBVType w) ->
    TestTemplate (BaseFloatType fpp)

  TFloatToBV :: (1 <= w) =>
    NatRepr w ->
    RoundingMode ->
    Bool {- False = unsigned -} ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseBVType w)

  TFloatCast ::
    FloatPrecisionRepr fpp ->
    RoundingMode ->
    TestTemplate (BaseFloatType fpp') ->
    TestTemplate (BaseFloatType fpp)

  TFloatToReal ::
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate BaseRealType

  TRealToFloat ::
    FloatPrecisionRepr fpp ->
    RoundingMode ->
    TestTemplate BaseRealType ->
    TestTemplate (BaseFloatType fpp)

  TFloatFMA ::
    RoundingMode ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseFloatType fpp) ->
    TestTemplate (BaseFloatType fpp)



instance Show (TestTemplate tp) where
  showsPrec d tt = case tt of
    TVar{}        -> showString "<var>"
    TFloatPZero{} -> showString "+0.0"
    TFloatNZero{} -> showString "-0.0"
    TFloatNaN{}   -> showString "NaN"
    TFloatUnOp op x -> showParen (d > 0) $
       shows op . showString " " . showsPrec 10 x
    TFloatBinOp op x y -> showParen (d > 0) $
       shows op . showString " " . showsPrec 10 x . showString " " . showsPrec 10 y
    TFloatTest op x -> showParen (d > 0) $
       shows op . showString " " . showsPrec 10 x
    TFloatRel op x y ->  showParen (d > 0) $
       shows op . showString " " . showsPrec 10 x . showString " " . showsPrec 10 y
    TFloatFMA r x y z -> showParen (d > 0) $
       showString "FMA" . showString " " . shows r . showString " " .
       showsPrec 10 x . showString " " . showsPrec 10 y . showString " " . showsPrec 10 z
    TFloatFromBits _fpp x -> showParen (d > 0) $
       showString "FloatFromBits " . showsPrec 10 x
    TFloatToBits x -> showParen (d > 0) $
       showString "FloatToBits " . showsPrec 10 x
    TFloatCast fpp r x -> showParen (d > 0) $
       showString "FloatCast " . shows fpp . showString " " . shows r . showString " " . showsPrec 10 x
    TFloatToReal x -> showParen (d > 0) $
       showString "FloatToReal " . showsPrec 10 x
    TRealToFloat fpp r x -> showParen (d > 0) $
       showString "RealToFloat " . shows fpp . showString " " . shows r . showString " " . showsPrec 10 x
    TBVToFloat fpp r sgn x ->
       showString (if sgn then "SBVToFloat " else "BVToFloat ") .
       shows fpp . showString " " .
       shows r . showString " " .
       showsPrec 10 x
    TFloatToBV w r sgn x ->
       showString (if sgn then "FloatToSBV" else "FloatToBV ") .
       shows w . showString " " .
       shows r . showString " " .
       showsPrec 10 x

-- | Compute the maximum depth of the given test template
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
          TFloatTest _op x    -> 1 + (f x)
          TFloatRel _op x y   -> 1 + max (f x) (f y)
          TFloatFMA _ x y z   -> 1 + max (f x) (max (f y) (f z))
          TFloatFromBits _ x  -> 1 + f x
          TFloatToBits x      -> 1 + f x
          TFloatCast _ _ x    -> 1 + f x
          TFloatToReal x      -> 1 + f x
          TRealToFloat _ _ x  -> 1 + f x
          TBVToFloat _ _ _ x  -> 1 + f x
          TFloatToBV _ _ _ x  -> 1 + f x


-- | A manually provided collection test templates that test coercions between types.
castTemplates :: RoundingMode -> [Some TestTemplate]
castTemplates r =
  [ Some (TFloatFromBits (knownRepr :: FloatPrecisionRepr Prec32) (TVar (BaseBVRepr (knownNat @32))))
  , Some (TFloatToBits (TVar (knownRepr :: BaseTypeRepr (BaseFloatType Prec32))))
  , Some (TFloatCast (knownRepr :: FloatPrecisionRepr Prec32) r
              (TVar (knownRepr :: BaseTypeRepr (BaseFloatType Prec64))))
  , Some (TFloatCast (knownRepr :: FloatPrecisionRepr Prec64) r
              (TVar (knownRepr :: BaseTypeRepr (BaseFloatType Prec32))))
  , Some (TFloatToReal (TVar (knownRepr :: BaseTypeRepr (BaseFloatType Prec32))))
  , Some (TRealToFloat (knownRepr :: FloatPrecisionRepr Prec32) r (TVar knownRepr))

  , Some (TBVToFloat (knownRepr :: FloatPrecisionRepr Prec32) r False
              (TVar (knownRepr :: BaseTypeRepr (BaseBVType 32))))
  , Some (TBVToFloat (knownRepr :: FloatPrecisionRepr Prec32) r True
              (TVar (knownRepr :: BaseTypeRepr (BaseBVType 32))))

  , Some (TFloatToBV (knownNat :: NatRepr 32) r False
              (TVar (knownRepr :: BaseTypeRepr (BaseFloatType Prec32))))
  , Some (TFloatToBV (knownNat :: NatRepr 32) r True
              (TVar (knownRepr :: BaseTypeRepr (BaseFloatType Prec32))))
  ]


-- | Generate test templates for all predicates and relations
--   on folating point values, whose subterms are generated
--   by calling @floatTemplates.  With the given inputs.
--
--   CAUTION! This function blows up very quickly!
floatTestTemplates ::
  [RoundingMode] ->
  Integer ->
  FloatPrecisionRepr fpp ->
  [TestTemplate BaseBoolType]
floatTestTemplates rs n fpp = tops <> relops
 where
   subterms = floatTemplates rs n fpp
   tops   = [ TFloatTest op x | op <- fTestOps, x <- subterms ]
   relops = [ TFloatRel op x y | op <- fRelOps, x <- subterms, y <- subterms ]

-- | Generate floating-point test templates of the given
--   depth, iterating through each of the given rounding
--   modes for operations that require rounding.
--
--   CAUTION! This function blows up very quickly!
floatTemplates ::
  [RoundingMode] ->
  Integer ->
  FloatPrecisionRepr fpp ->
  [TestTemplate (BaseFloatType fpp)]
floatTemplates rs n fpp
  | n <= 0 = base
  | n == 1 = base <> floatOps fpp rs base
  | otherwise = f n

  where
   base = [ TVar (BaseFloatRepr fpp), TFloatPZero fpp, TFloatNZero fpp, TFloatNaN fpp ]

   f d | d < 1 = [ TVar (BaseFloatRepr fpp) ]
   f d = [ TVar (BaseFloatRepr fpp) ] <> floatOps fpp rs (f (d-1))

floatOps ::
  FloatPrecisionRepr fpp ->
  [RoundingMode] ->
  [TestTemplate (BaseFloatType fpp)] ->
  [TestTemplate (BaseFloatType fpp)]
floatOps fpp@(FloatingPointPrecisionRepr eb sb) rs subterms = casts <> uops <> bops <> fma
  where
    uops  = [ TFloatUnOp op x | op <- fUnOps rs, x <- subterms ]
    bops  = [ TFloatBinOp op x y | op <- fBinOps rs, x <- subterms, y <- subterms ]
    fma   = [ TFloatFMA r x y z | r <- rs, x <- subterms, y <- subterms, z <- subterms ]
    casts = [ case isPosNat (addNat eb sb) of
                Just LeqProof -> TFloatFromBits fpp (TVar (BaseBVRepr (addNat eb sb)))
                Nothing -> error $ unwords ["floatOps", "bad fpp", show fpp]
            ]

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

fTestOps :: [FTestOp]
fTestOps = [ FIsNaN, FIsInf, FIsZero, FIsPos, FIsNeg, FIsSubnorm, FIsNorm ]

fRelOps :: [FRelOp]
fRelOps = [ FLogicEq, FLogicNeq, FEq, FApart, FUnordered, FLe, FLt, FGe, FGt ]



generateByType :: BaseTypeRepr tp -> Gen (GroundValue tp)
generateByType BaseBoolRepr = Gen.bool
generateByType (BaseFloatRepr fpp) = genFloat fpp
generateByType (BaseBVRepr w) = genBV w
generateByType BaseRealRepr  = genReal
generateByType tp = error ("generateByType! TODO " ++ show tp)

genReal :: Gen Rational
genReal = Gen.realFrac_ (Gen.linearFracFrom 0 (negate mx) mx)
  where mx = 1 ^^ (200::Integer)

genBV :: (1 <= w) => NatRepr w -> Gen (BV.BV w)
genBV w =
  do val <- Gen.integral (Gen.linearFrom 0 (minSigned w) (maxSigned w))
     pure (BV.mkBV w val)

-- | A random generator for floating-point values that tries to
--   get good coverage for all the various special and normal values.
genFloat :: FloatPrecisionRepr fpp -> Gen BigFloat
genFloat (FloatingPointPrecisionRepr eb sb) =
    Gen.frequency
        [ ( 1, pure bfPosZero)
        , ( 1, pure bfNegZero)
        , ( 1, pure bfPosInf)
        , ( 1, pure bfNegInf)
        , ( 1, pure bfNaN)
        , (50, genNormal)
        , ( 5, genSubnormal)
        , (45, genBinary)
        ]
 where
  emax = bit (fromInteger (intValue eb - 1)) - 1
  smax = bit (fromInteger (intValue sb)) - 1
  opts = fpOpts (intValue eb) (intValue sb) Away
  numBits = intValue eb + intValue sb

  -- generates non-shrinkable floats uniformly chosen from among all bitpatterns
  genBinary =
    do bits <- Gen.integral_ (Gen.linear 0 (bit (fromInteger numBits) - 1))
       pure (bfFromBits opts bits)

  -- generates non-shrinkable floats corresponding to subnormal values.  These are
  -- values with 0 biased exponent and nonzero mantissa.
  genSubnormal =
    do sgn  <- Gen.bool
       bits <- Gen.integral_ (Gen.linear 1 (bit (fromInteger (intValue sb)) - 1))
       let x0 = bfFromBits opts bits
       let x  = if sgn then bfNeg x0 else x0
       pure $! x

  -- tries to generate shrinkable floats, prefering "smaller" values
  genNormal =
    do sgn <- Gen.bool
       ex  <- Gen.integral (Gen.linearFrom 0 (1-emax) emax)
       mag <- Gen.integral (Gen.linear 1 smax)
       let x0 = bfStatus (bfMul2Exp opts (bfFromInteger mag) (ex - fromIntegral (lgCeil mag)))
       let x  = if sgn then bfNeg x0 else x0
       pure $! x

-- | Use the given map to bind the values in an expression and compute the value
--   of the expression, if it can be computed.
mapGroundEval :: MapF (Expr t) GroundValueWrapper -> Expr t tp -> MaybeT IO (GroundValue tp)
mapGroundEval m x =
  case MapF.lookup x m of
    Just v -> pure (unGVW v)
    Nothing -> tryEvalGroundExpr (mapGroundEval m) x

-- | Inject ground values into expressions based on their type.
groundLit ::  ExprBuilder t st fs -> BaseTypeRepr tp -> GroundValue tp -> IO (Expr t tp)
groundLit sym tp v =
  case tp of
    BaseFloatRepr fpp -> floatLit sym fpp v
    BaseBVRepr w      -> bvLit sym w v
    BaseBoolRepr      -> pure (backendPred sym v)
    BaseRealRepr      -> realLit sym v
    _ -> error $ unwords ["groundLit TODO", show tp]

-- | Given a map binding varables to expressions, rebuild the given expression by reapplying
--   the expression formers appearing in it.  This is used to test the constant-folding
--   rules of the expression builder.
reduceEval :: ExprBuilder t st fs -> MapF (Expr t) GroundValueWrapper -> Expr t tp -> IO (Expr t tp)
reduceEval sym m e
  | Just v <- MapF.lookup e m = groundLit sym (exprType e) (unGVW v)
  | Just a <- asApp e = reduceApp sym bvUnary =<< traverseApp (reduceEval sym m) a
  | otherwise = pure e

-- | Use the given solver process as an evaluation oracle to
--   verify that a given expression must have the given
--   value when the variables in it are bound via the
--   given map.
--
--   A value as computed via @solverEval@ may nonetheless fail
--   this test if functions appearing in it are underconstrained.
verifySolverEval :: forall t st fs solver tp.
  OnlineSolver solver =>
  ExprBuilder t st fs ->
  SolverProcess t solver ->
  MapF (Expr t) GroundValueWrapper ->
  Expr t tp ->
  GroundValue tp ->
  IO Bool
verifySolverEval _sym proc gmap expr val =
  do let c = Online.solverConn proc
     let f :: Pair (Expr t) GroundValueWrapper -> IO (SMT.Term solver)
         f (Pair e (GVW v)) =
            case exprType e of
              BaseFloatRepr fpp ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.floatTerm fpp v)
              BaseBVRepr w ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.bvTerm w v)
              BaseBoolRepr ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.boolExpr v)
              BaseRealRepr ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.rationalTerm v)

              tp -> fail ("verifySolverEval: TODO " ++ show tp)

     Online.inNewFrame proc do
       mapM_ (SMT.assumeFormula c <=< f) (MapF.toList gmap)

       gl <- f (Pair expr (GVW val))
       SMT.assumeFormula c (SMT.notExpr gl)

       res <- Online.check proc "eval"
       case res of
         Unknown -> fail "Expected UNSAT, but got UNKNOWN"
         Unsat _ -> pure True
         Sat _   -> pure False

-- | Use the given solver process as an evaluation oracle to
--   compute the a value of the given expression when given
--   a binding of variables that appear in the expression.
--   Return the value computed by the solver.
--
--   In principle, the solver might return one of several
--   different values for the expression if any of the
--   functions appearing in it are partial or underspecified.
solverEval :: forall t st fs solver tp.
  OnlineSolver solver =>
  ExprBuilder t st fs ->
  SolverProcess t solver ->
  MapF (Expr t) GroundValueWrapper ->
  Expr t tp ->
  IO (GroundValue tp)
solverEval _sym proc gmap expr =
  do let c = Online.solverConn proc
     let f :: Pair (Expr t) GroundValueWrapper -> IO (SMT.Term solver)
         f (Pair e (GVW v)) =
            case exprType e of
              BaseFloatRepr fpp ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.floatTerm fpp v)
              BaseBVRepr w ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.bvTerm w v)
              BaseBoolRepr ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.boolExpr v)
              BaseRealRepr ->
                do e' <- mkSMTTerm c e
                   return (e' .== SMT.rationalTerm v)

              tp -> fail ("solverEval: TODO " ++ show tp)

     Online.inNewFrame proc do
       mapM_ (SMT.assumeFormula c <=< f) (MapF.toList gmap)
       e' <- mkSMTTerm c expr
       res <- Online.check proc "eval"
       case res of
         Unsat _ -> fail "Expected SAT, but got UNSAT"
         Unknown -> fail "Expected SAT, but got UNKNOWN"
         Sat _ ->
           case exprType expr of
             BaseFloatRepr fpp ->
               do bv <- SMT.smtEvalFloat (Online.solverEvalFuns proc) fpp e'
                  return (bfFromBits (fppOpts fpp RNE) (BV.asUnsigned bv))
             BaseBVRepr w ->
               SMT.smtEvalBV (Online.solverEvalFuns proc) w e'
             BaseRealRepr ->
               SMT.smtEvalReal (Online.solverEvalFuns proc) e'
             BaseBoolRepr ->
               SMT.smtEvalBool (Online.solverEvalFuns proc) e'

             tp -> fail ("solverEval: TODO2 " ++ show tp)

showMap :: MapF (Expr t) GroundValueWrapper -> String
showMap gmap = unlines (map f (MapF.toList gmap))
  where
    f :: Pair (Expr t) (GroundValueWrapper) -> String
    f (Pair e (GVW v)) = show (printSymExpr e) <> " |-> " <> showGroundVal (exprType e) v

showGroundVal :: HasCallStack => BaseTypeRepr tp -> GroundValue tp -> String
showGroundVal tp v =
  case tp of
    BaseFloatRepr fpp ->
      let i = bfToBits (fppOpts fpp RNE) v in
        show v <> " 0x" <> showHex i ""
    BaseBVRepr w -> BV.ppHex w v
    BaseRealRepr -> show v
    BaseBoolRepr -> show v
    _ -> "showGroundVal: TODO " <> show tp

-- | This property generator takes a template and uses it to
--   compare our Haskell-side ground evaulation code against
--   the computations performed by an online solver, which
--   is used as a computational oracle.  Random values are
--   chosen for the free variables, and the expression is evaluated
--   by the ground evaluator using the generated values for
--   the variables.  Next, in the solver, we assert the equality of
--   the same variables to their concrete values and ask for a satisfying
--   model; then we ask the solver for the value of the expression in
--   that model and check that the two computations agree.
--
--   Some expressions are underspecified, which means their output is
--   unconstrained for some inputs (e.g, division by 0). In these cases
--   the ground evaluator may compute no value at all; these cases
--   are considered successful tests.
templateGroundEvalTest ::
  OnlineSolver solver =>
  ExprBuilder t st fs ->
  SolverProcess t solver ->
  TestTemplate tp ->
  Int ->
  IO Property
templateGroundEvalTest sym proc t numTests =
  do (sz, gmapGen, expr) <- templateGen sym t
     pure $ withTests (fromIntegral (max 1 (numTests * sz))) $ property $
       do annotateShow (printSymExpr expr)
          gmap <- forAllWith showMap gmapGen
          v  <- liftIO (runMaybeT (mapGroundEval gmap expr))
          annotate (maybe "Nothing" (showGroundVal (exprType expr)) v)
          res <- liftIO (try (solverEval sym proc gmap expr))
          case res of
            Left (ex :: IOError) -> footnote (show ex) >> failure
            Right v' ->
              do annotate (showGroundVal (exprType expr) v')
                 case v of
                   Just v_ -> Just True === groundEq (exprType expr) v_ v'
                   Nothing -> success

-- | This property generator takes a template and uses it to
--   compare our Haskell-side ground evaulation code against
--   the computations performed by an online solver, which
--   is used as a computational oracle.  Random values are
--   chosen for the free variables, and the expression is evaluated
--   by the ground evaluator using the generated values for
--   the variables.  Next, in the solver, we assert the equality of
--   the same variables to their concrete values, and ask the solver
--   to prove that it has the same value as we computed in the
--   ground evaluator.  This complements the above test; together
--   they demonstrate that the ground evaluator, when it computes a
--   value at all, computes the unique value that a solver may assign to it.
templateGroundEvalTestAlt ::
  OnlineSolver solver =>
  ExprBuilder t st fs ->
  SolverProcess t solver ->
  TestTemplate tp ->
  Int ->
  IO Property
templateGroundEvalTestAlt sym proc t numTests =
  do (sz, gmapGen, expr) <- templateGen sym t
     pure $ withTests (fromIntegral (max 1 (numTests * sz))) $ property $
       do annotateShow (printSymExpr expr)
          gmap <- forAllWith showMap gmapGen
          v  <- liftIO (runMaybeT (mapGroundEval gmap expr))
          case v of
            Nothing -> success
            Just v_ ->
              do annotate (showGroundVal (exprType expr) v_)
                 res <- liftIO (try (verifySolverEval sym proc gmap expr v_))
                 case res of
                   Left (ex :: IOError) -> footnote (show ex) >> failure
                   Right b -> if b then success else failure


-- | This property generator takes a template and uses it to
--   compare the ground evaluation code against the constant-folding
--   rules used when constructing terms.  Similar to the test above,
--   we compute an expression and then use ground evaluation to
--   compute a value for randomly-chosen values of the variables.
--   Next, we \"reduce\" the expression by reapplying the syntactic
--   constructors, replacing the variables with literal expressions.
--   Finally, we check that the expression has constant-folded to
--   a literal expression that agrees with the ground value computed
--   before. Moreover, ground evaluation should fail to compute a value
--   iff the reduced expression does not constant-fold to a literal.
templateConstantFoldTest ::
  ExprBuilder t st fs ->
  TestTemplate tp ->
  Int ->
  IO Property
templateConstantFoldTest sym t numTests =
  do (sz, gmapGen, expr) <- templateGen sym t
     pure $ withTests (fromIntegral (max 1 (numTests * sz))) $ property $
       do annotateShow (printSymExpr expr)
          gmap <- forAllWith showMap gmapGen

          v  <- liftIO (runMaybeT (mapGroundEval gmap expr))
          annotate (maybe "Nothing" (showGroundVal (exprType expr)) v)

          v' <- liftIO (reduceEval sym gmap expr)
          annotateShow (printSymExpr v')

          case v of
            Just v_ ->
              do p <- liftIO (isEq sym v' =<< groundLit sym (exprType expr) v_)
                 Just True === asConstantPred p
            Nothing -> False === baseIsConcrete v'

-- | Given a test template, compute data that can be used to drive one of the
--   test predicates above.  We return an @Int@ that counts how many variables
--   appear in the template, a generator action that computes ground values
--   for the variables appearing in the template, and an expression over
--   those variables according to the template.
templateGen :: forall t st fs tp.
  ExprBuilder t st fs -> TestTemplate tp -> IO (Int, Gen (MapF (Expr t) GroundValueWrapper), Expr t tp)
templateGen sym = f
  where
    f :: forall tp'. TestTemplate tp' -> IO (Int, Gen (MapF (Expr t) GroundValueWrapper), Expr t tp')
    f (TVar bt) =
       do v <- freshConstant sym emptySymbol bt
          return (1, MapF.singleton v . GVW <$> generateByType bt, v)

    f (TFloatPZero fpp) =
       do e <- floatPZero sym fpp
          return (0, pure MapF.empty, e)

    f (TFloatNZero fpp) =
       do e <- floatNZero sym fpp
          return (0, pure MapF.empty, e)

    f (TFloatNaN fpp) =
        do e <- floatNaN sym fpp
           return (0, pure MapF.empty, e)

    f (TFloatUnOp op x) =
        do (xn,xg,xe) <- f x
           e <- case op of
                  FNeg     -> floatNeg sym xe
                  FAbs     -> floatAbs sym xe
                  FSqrt  r -> floatSqrt sym r xe
                  FRound r -> floatRound sym r xe
           return (xn,xg, e)

    f (TFloatBinOp op x y) =
        do (xn,xg,xe) <- f x
           (yn,yg,ye) <- f y
           e <- case op of
                  FAdd r -> floatAdd sym r xe ye
                  FSub r -> floatSub sym r xe ye
                  FMul r -> floatMul sym r xe ye
                  FDiv r -> floatDiv sym r xe ye
                  FRem   -> floatRem sym xe ye
                  FMin   -> floatMin sym xe ye
                  FMax   -> floatMax sym xe ye

           return (xn+yn, MapF.union <$> xg <*> yg, e)

    f (TFloatTest op x) =
        do (xn,xg,xe) <- f x
           e <- case op of
                  FIsNaN  -> floatIsNaN sym xe
                  FIsInf  -> floatIsInf sym xe
                  FIsZero -> floatIsZero sym xe
                  FIsPos  -> floatIsPos sym xe
                  FIsNeg  -> floatIsNeg sym xe
                  FIsSubnorm -> floatIsSubnorm sym xe
                  FIsNorm -> floatIsNorm sym xe
           return (xn, xg, e)

    f (TFloatRel op x y) =
        do (xn,xg,xe) <- f x
           (yn,yg,ye) <- f y
           e <- case op of
                  FLogicEq   -> floatEq sym xe ye
                  FLogicNeq  -> floatNe sym xe ye
                  FEq        -> floatFpEq sym xe ye
                  FApart     -> floatFpApart sym xe ye
                  FUnordered -> floatFpUnordered sym xe ye
                  FLe        -> floatLe sym xe ye
                  FLt        -> floatLt sym xe ye
                  FGe        -> floatGe sym xe ye
                  FGt        -> floatGt sym xe ye

           return (xn+yn, MapF.union <$> xg <*> yg, e)

    f (TFloatFMA r x y z) =
        do (xn,xg,xe) <- f x
           (yn,yg,ye) <- f y
           (zn,zg,ze) <- f z
           e <- floatFMA sym r xe ye ze
           return (xn+yn+zn, foldr MapF.union MapF.empty <$> sequence [xg,yg,zg], e)

    f (TFloatFromBits fpp x) =
        do (xn,xg,xe) <- f x
           e <- floatFromBinary sym fpp xe
           return (xn,xg,e)

    f (TFloatToBits x) =
        do (xn,xg,xe) <- f x
           e <- floatToBinary sym xe
           return (xn,xg,e)

    f (TFloatCast fpp r x) =
        do (xn,xg,xe) <- f x
           e <- floatCast sym fpp r xe
           return (xn,xg,e)

    f (TFloatToReal x) =
        do (xn,xg,xe) <- f x
           e <- floatToReal sym xe
           return (xn,xg,e)

    f (TRealToFloat fpp r x) =
        do (xn,xg,xe) <- f x
           e <- realToFloat sym fpp r xe
           return (xn,xg,e)

    f (TBVToFloat fpp r sgn x) =
        do (xn,xg,xe) <- f x
           e <- case sgn of
                  False -> bvToFloat sym fpp r xe
                  True  -> sbvToFloat sym fpp r xe
           return (xn,xg,e)

    f (TFloatToBV w r sgn x) =
        do (xn,xg,xe) <- f x
           e <- case sgn of
                  False -> floatToBV sym w r xe
                  True  -> floatToSBV sym w r xe
           return (xn,xg,e)
