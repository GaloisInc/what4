------------------------------------------------------------------------
-- |
-- Module      : What4.Expr.GroundEval
-- Description : Computing ground values for expressions from solver assignments
-- Copyright   : (c) Galois, Inc 2016-2020
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
--
-- Given a collection of assignments to the symbolic values appearing in
-- an expression, this module computes the ground value.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module What4.Expr.GroundEval
  ( -- * Ground evaluation
    GroundValue
  , GroundValueWrapper(..)
  , GroundArray(..)
  , lookupArray
  , GroundEvalFn(..)
  , ExprRangeBindings

    -- * Internal operations
  , tryEvalGroundExpr
  , evalGroundExpr
  , evalGroundApp
  , evalGroundNonceApp
  , defaultValueForType
  , groundEq
  ) where

import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import qualified Data.BitVector.Sized as BV
import           Data.List (foldl')
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           LibBF (BigFloat)
import qualified LibBF as BF

import           What4.BaseTypes
import           What4.Interface
import qualified What4.SemiRing as SR
import qualified What4.Expr.ArrayUpdateMap as AUM
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.Builder
import qualified What4.Expr.StringSeq as SSeq
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.UnaryBV as UnaryBV

import           What4.Utils.Arithmetic ( roundAway )
import           What4.Utils.Complex
import           What4.Utils.FloatHelpers
import           What4.Utils.StringLiteral


type family GroundValue (tp :: BaseType) where
  GroundValue BaseBoolType          = Bool
  GroundValue BaseIntegerType       = Integer
  GroundValue BaseRealType          = Rational
  GroundValue (BaseBVType w)        = BV.BV w
  GroundValue (BaseFloatType fpp)   = BigFloat
  GroundValue BaseComplexType       = Complex Rational
  GroundValue (BaseStringType si)   = StringLiteral si
  GroundValue (BaseArrayType idx b) = GroundArray idx b
  GroundValue (BaseStructType ctx)  = Ctx.Assignment GroundValueWrapper ctx

-- | A function that calculates ground values for elements.
--   Clients of solvers should use the @groundEval@ function for computing
--   values in models.
newtype GroundEvalFn t = GroundEvalFn { groundEval :: forall tp . Expr t tp -> IO (GroundValue tp) }

-- | Function that calculates upper and lower bounds for real-valued elements.
--   This type is used for solvers (e.g., dReal) that give only approximate solutions.
type ExprRangeBindings t = RealExpr t -> IO (Maybe Rational, Maybe Rational)

-- | A newtype wrapper around ground value for use in a cache.
newtype GroundValueWrapper tp = GVW { unGVW :: GroundValue tp }

-- | A representation of a ground-value array.
data GroundArray idx b
  = ArrayMapping (Ctx.Assignment GroundValueWrapper idx -> IO (GroundValue b))
    -- ^ Lookup function for querying by index
  | ArrayConcrete (GroundValue b) (Map.Map (Ctx.Assignment IndexLit idx) (GroundValue b))
    -- ^ Default value and finite map of particular indices

-- | Look up an index in an ground array.
lookupArray :: Ctx.Assignment BaseTypeRepr idx
            -> GroundArray idx b
            -> Ctx.Assignment GroundValueWrapper idx
            -> IO (GroundValue b)
lookupArray _ (ArrayMapping f) i = f i
lookupArray tps (ArrayConcrete base m) i = return $ fromMaybe base (Map.lookup i' m)
  where i' = fromMaybe (error "lookupArray: not valid indexLits") $ Ctx.zipWithM asIndexLit tps i

asIndexLit :: BaseTypeRepr tp -> GroundValueWrapper tp -> Maybe (IndexLit tp)
asIndexLit BaseIntegerRepr (GVW v) = return $ IntIndexLit v
asIndexLit (BaseBVRepr w)  (GVW v) = return $ BVIndexLit w v
asIndexLit _ _ = Nothing

-- | Convert a real standardmodel val to a double.
toDouble :: Rational -> Double
toDouble = fromRational

fromDouble :: Double -> Rational
fromDouble = toRational

-- | Construct a default value for a given base type.
defaultValueForType :: BaseTypeRepr tp -> GroundValue tp
defaultValueForType tp =
  case tp of
    BaseBoolRepr    -> False
    BaseBVRepr w    -> BV.zero w
    BaseIntegerRepr -> 0
    BaseRealRepr    -> 0
    BaseComplexRepr -> 0 :+ 0
    BaseStringRepr si -> stringLitEmpty si
    BaseArrayRepr _ b -> ArrayConcrete (defaultValueForType b) Map.empty
    BaseStructRepr ctx -> fmapFC (GVW . defaultValueForType) ctx
    BaseFloatRepr _fpp -> BF.bfPosZero

{-# INLINABLE evalGroundExpr #-}
-- | Helper function for evaluating @Expr@ expressions in a model.
--
--   This function is intended for implementers of symbolic backends.
evalGroundExpr :: (forall u . Expr t u -> IO (GroundValue u))
              -> Expr t tp
              -> IO (GroundValue tp)
evalGroundExpr f e =
 runMaybeT (tryEvalGroundExpr (lift . f) e) >>= \case
    Just x -> return x

    Nothing
      | BoundVarExpr v <- e ->
          case bvarKind v of
            QuantifierVarKind -> fail $ "The ground evaluator does not support bound variables."
            LatchVarKind      -> return $! defaultValueForType (bvarType v)
            UninterpVarKind   -> return $! defaultValueForType (bvarType v)
      | otherwise -> fail $ unwords ["evalGroundExpr: could not evaluate expression:", show e]


{-# INLINABLE tryEvalGroundExpr #-}
-- | Evaluate an element, when given an evaluation function for
--   subelements.  Instead of recursing directly, `tryEvalGroundExpr`
--   calls into the given function on sub-elements to allow the caller
--   to cache results if desired.
--
--   However, sometimes we are unable to compute expressions outside
--   the solver.  In these cases, this function will return `Nothing`
--   in the `MaybeT IO` monad.  In these cases, the caller should instead
--   query the solver directly to evaluate the expression, if possible.
tryEvalGroundExpr :: (forall u . Expr t u -> MaybeT IO (GroundValue u))
                 -> Expr t tp
                 -> MaybeT IO (GroundValue tp)
tryEvalGroundExpr _ (SemiRingLiteral SR.SemiRingIntegerRepr c _) = return c
tryEvalGroundExpr _ (SemiRingLiteral SR.SemiRingRealRepr c _) = return c
tryEvalGroundExpr _ (SemiRingLiteral (SR.SemiRingBVRepr _ _ ) c _) = return c
tryEvalGroundExpr _ (StringExpr x _)  = return x
tryEvalGroundExpr _ (BoolExpr b _)    = return b
tryEvalGroundExpr _ (FloatExpr _ f _) = return f
tryEvalGroundExpr f (NonceAppExpr a0) = evalGroundNonceApp f (nonceExprApp a0)
tryEvalGroundExpr f (AppExpr a0)      = evalGroundApp f (appExprApp a0)
tryEvalGroundExpr _ (BoundVarExpr _)  = mzero

{-# INLINABLE evalGroundNonceApp #-}
-- | Helper function for evaluating @NonceApp@ expressions.
--
--   This function is intended for implementers of symbolic backends.
evalGroundNonceApp :: Monad m
                   => (forall u . Expr t u -> MaybeT m (GroundValue u))
                   -> NonceApp t (Expr t) tp
                   -> MaybeT m (GroundValue tp)
evalGroundNonceApp fn a0 =
  case a0 of
    Annotation _ _ t -> fn t
    Forall{} -> mzero
    Exists{} -> mzero
    MapOverArrays{} -> mzero
    ArrayFromFn{} -> mzero
    ArrayTrueOnEntries{} -> mzero
    FnApp{} -> mzero

{-# INLINABLE evalGroundApp #-}

forallIndex :: Ctx.Size (ctx :: Ctx.Ctx k) -> (forall tp . Ctx.Index ctx tp -> Bool) -> Bool
forallIndex sz f = Ctx.forIndex sz (\b j -> f j && b) True


newtype MAnd x = MAnd { unMAnd :: Maybe Bool }
instance Functor MAnd where
  fmap _f (MAnd x) = MAnd x
instance Applicative MAnd where
  pure _ = MAnd (Just True)
  MAnd (Just a) <*> MAnd (Just b) = MAnd (Just $! (a && b))
  _ <*> _ = MAnd Nothing

mand :: Bool -> MAnd z
mand = MAnd . Just

coerceMAnd :: MAnd a -> MAnd b
coerceMAnd (MAnd x) = MAnd x

groundEq :: BaseTypeRepr tp -> GroundValue tp -> GroundValue tp -> Maybe Bool
groundEq bt0 x0 y0 = unMAnd (f bt0 x0 y0)
  where
    f :: BaseTypeRepr tp -> GroundValue tp -> GroundValue tp -> MAnd z
    f bt x y = case bt of
      BaseBoolRepr     -> mand $ x == y
      BaseRealRepr     -> mand $ x == y
      BaseIntegerRepr  -> mand $ x == y
      BaseBVRepr _     -> mand $ x == y
      -- NB, don't use (==) for BigFloat, which is the wrong equality
      BaseFloatRepr _  -> mand $ BF.bfCompare x y == EQ
      BaseStringRepr _ -> mand $ x == y
      BaseComplexRepr  -> mand $ x == y
      BaseStructRepr flds ->
        coerceMAnd (Ctx.traverseWithIndex
          (\i tp -> f tp (unGVW (x Ctx.! i)) (unGVW (y Ctx.! i))) flds)
      BaseArrayRepr{} -> MAnd Nothing

-- | Helper function for evaluating @App@ expressions.
--
--   This function is intended for implementers of symbolic backends.
evalGroundApp :: forall t tp
               . (forall u . Expr t u -> MaybeT IO (GroundValue u))
              -> App (Expr t) tp
              -> MaybeT IO (GroundValue tp)
evalGroundApp f a0 = do
  case a0 of
    BaseEq bt x y ->
      do x' <- f x
         y' <- f y
         MaybeT (return (groundEq bt x' y'))

    BaseIte _ _ x y z -> do
      xv <- f x
      if xv then f y else f z

    NotPred x -> not <$> f x
    ConjPred xs ->
      let pol (x,Positive) = f x
          pol (x,Negative) = not <$> f x
      in
      case BM.viewBoolMap xs of
        BM.BoolMapUnit -> return True
        BM.BoolMapDualUnit -> return False
        BM.BoolMapTerms (t:|ts) ->
          foldl' (&&) <$> pol t <*> mapM pol ts

    RealIsInteger x -> (\xv -> denominator xv == 1) <$> f x
    BVTestBit i x ->
        BV.testBit' i <$> f x
    BVSlt x y -> BV.slt w <$> f x <*> f y
      where w = bvWidth x
    BVUlt x y -> BV.ult <$> f x <*> f y

    IntDiv x y -> g <$> f x <*> f y
      where
      g u v | v == 0    = 0
            | v >  0    = u `div` v
            | otherwise = negate (u `div` negate v)

    IntMod x y -> intModu <$> f x <*> f y
      where intModu _ 0 = 0
            intModu i v = fromInteger (i `mod` abs v)

    IntAbs x -> fromInteger . abs <$> f x

    IntDivisible x k -> g <$> f x
      where
      g u | k == 0    = u == 0
          | otherwise = mod u (toInteger k) == 0

    SemiRingLe SR.OrderedSemiRingRealRepr    x y -> (<=) <$> f x <*> f y
    SemiRingLe SR.OrderedSemiRingIntegerRepr x y -> (<=) <$> f x <*> f y

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingIntegerRepr -> WSum.evalM (\x y -> pure (x+y)) smul pure s
           where smul sm e = (sm *) <$> f e
        SR.SemiRingRealRepr -> WSum.evalM (\x y -> pure (x+y)) smul pure s
           where smul sm e = (sm *) <$> f e
        SR.SemiRingBVRepr SR.BVArithRepr w -> WSum.evalM sadd smul pure s
           where
           smul sm e = BV.mul w sm <$> f e
           sadd x y  = pure (BV.add w x y)
        SR.SemiRingBVRepr SR.BVBitsRepr _w -> WSum.evalM sadd smul pure s
           where
           smul sm e = BV.and sm <$> f e
           sadd x y  = pure (BV.xor x y)

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingIntegerRepr -> fromMaybe 1 <$> WSum.prodEvalM (\x y -> pure (x*y)) f pd
        SR.SemiRingRealRepr    -> fromMaybe 1 <$> WSum.prodEvalM (\x y -> pure (x*y)) f pd
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          fromMaybe (BV.one w) <$> WSum.prodEvalM (\x y -> pure (BV.mul w x y)) f pd
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          fromMaybe (BV.maxUnsigned w) <$> WSum.prodEvalM (\x y -> pure (BV.and x y)) f pd

    RealDiv x y -> do
      xv <- f x
      yv <- f y
      return $!
        if yv == 0 then 0 else xv / yv
    RealSqrt x -> do
      xv <- f x
      when (xv < 0) $ do
        lift $ fail $ "Model returned sqrt of negative number."
      return $ fromDouble (sqrt (toDouble xv))

    ------------------------------------------------------------------------
    -- Operations that introduce irrational numbers.

    Pi -> return $ fromDouble pi
    RealSin x -> fromDouble . sin . toDouble <$> f x
    RealCos x -> fromDouble . cos . toDouble <$> f x
    RealATan2 x y -> do
      xv <- f x
      yv <- f y
      return $ fromDouble (atan2 (toDouble xv) (toDouble yv))
    RealSinh x -> fromDouble . sinh . toDouble <$> f x
    RealCosh x -> fromDouble . cosh . toDouble <$> f x

    RealExp x -> fromDouble . exp . toDouble <$> f x
    RealLog x -> fromDouble . log . toDouble <$> f x

    ------------------------------------------------------------------------
    -- Bitvector Operations

    BVOrBits w bs -> foldl' BV.or (BV.zero w) <$> traverse f (bvOrToList bs)
    BVUnaryTerm u ->
      BV.mkBV (UnaryBV.width u) <$> UnaryBV.evaluate f u
    BVConcat _w x y -> BV.concat (bvWidth x) (bvWidth y) <$> f x <*> f y
    BVSelect idx n x -> BV.select idx n <$> f x
    BVUdiv w x y -> myDiv <$> f x <*> f y
      where myDiv _ (BV.BV 0) = BV.zero w
            myDiv u v = BV.uquot u v
    BVUrem _w x y -> myRem <$> f x <*> f y
      where myRem u (BV.BV 0) = u
            myRem u v = BV.urem u v
    BVSdiv w x y -> myDiv <$> f x <*> f y
      where myDiv _ (BV.BV 0) = BV.zero w
            myDiv u v = BV.sdiv w u v
    BVSrem w x y -> myRem <$> f x <*> f y
      where myRem u (BV.BV 0) = u
            myRem u v = BV.srem w u v
    BVShl  w x y  -> BV.shl w  <$> f x <*> (BV.asNatural <$> f y)
    BVLshr w x y -> BV.lshr w <$> f x <*> (BV.asNatural <$> f y)
    BVAshr w x y  -> BV.ashr w <$> f x <*> (BV.asNatural <$> f y)
    BVRol w x y -> BV.rotateL w <$> f x <*> (BV.asNatural <$> f y)
    BVRor w x y -> BV.rotateR w <$> f x <*> (BV.asNatural <$> f y)

    BVZext w x -> BV.zext w <$> f x
    -- BGS: This check can be proven to GHC
    BVSext w x ->
      case isPosNat w of
        Just LeqProof -> BV.sext (bvWidth x) w <$> f x
        Nothing -> error "BVSext given bad width"

    BVFill w p ->
      do b <- f p
         return $! if b then BV.maxUnsigned w else BV.zero w

    BVPopcount _w x ->
      BV.popCount <$> f x
    BVCountLeadingZeros w x ->
      BV.clz w <$> f x
    BVCountTrailingZeros w x ->
      BV.ctz w <$> f x

    ------------------------------------------------------------------------
    -- Floating point Operations

    FloatNeg _fpp x    -> BF.bfNeg <$> f x
    FloatAbs _fpp x    -> BF.bfAbs <$> f x
    FloatSqrt fpp r x  -> bfStatus . BF.bfSqrt (fppOpts fpp r) <$> f x
    FloatRound fpp r x -> floatRoundToInt fpp r <$> f x

    FloatAdd fpp r x y -> bfStatus <$> (BF.bfAdd (fppOpts fpp r) <$> f x <*> f y)
    FloatSub fpp r x y -> bfStatus <$> (BF.bfSub (fppOpts fpp r) <$> f x <*> f y)
    FloatMul fpp r x y -> bfStatus <$> (BF.bfMul (fppOpts fpp r) <$> f x <*> f y)
    FloatDiv fpp r x y -> bfStatus <$> (BF.bfDiv (fppOpts fpp r) <$> f x <*> f y)
    FloatRem fpp   x y -> bfStatus <$> (BF.bfRem (fppOpts fpp RNE) <$> f x <*> f y)
    FloatFMA fpp r x y z -> bfStatus <$> (BF.bfFMA (fppOpts fpp r) <$> f x <*> f y <*> f z)

    FloatFpEq x y      -> (==) <$> f x <*> f y -- NB, IEEE754 equality
    FloatLe   x y      -> (<=) <$> f x <*> f y
    FloatLt   x y      -> (<)  <$> f x <*> f y

    FloatIsNaN  x -> BF.bfIsNaN  <$> f x
    FloatIsZero x -> BF.bfIsZero <$> f x
    FloatIsInf  x -> BF.bfIsInf  <$> f x
    FloatIsPos  x -> BF.bfIsPos  <$> f x
    FloatIsNeg  x -> BF.bfIsNeg  <$> f x

    FloatIsNorm x ->
      case exprType x of
        BaseFloatRepr fpp ->
          BF.bfIsNormal (fppOpts fpp RNE) <$> f x

    FloatIsSubnorm x ->
      case exprType x of
        BaseFloatRepr fpp ->
          BF.bfIsSubnormal (fppOpts fpp RNE) <$> f x

    FloatFromBinary fpp x ->
      BF.bfFromBits (fppOpts fpp RNE) . BV.asUnsigned <$> f x

    FloatToBinary fpp@(FloatingPointPrecisionRepr eb sb) x ->
      BV.mkBV (addNat eb sb) . BF.bfToBits (fppOpts fpp RNE) <$> f x

    FloatCast fpp r x -> bfStatus . BF.bfRoundFloat (fppOpts fpp r) <$> f x

    RealToFloat fpp r x -> floatFromRational (fppOpts fpp r) <$> f x
    BVToFloat   fpp r x -> floatFromInteger (fppOpts fpp r) . BV.asUnsigned <$> f x
    SBVToFloat  fpp r x -> floatFromInteger (fppOpts fpp r) . BV.asSigned (bvWidth x) <$> f x

    FloatToReal x -> MaybeT . pure . floatToRational =<< f x

    FloatToBV w r x ->
      do z <- floatToInteger r <$> f x
         case z of
           Just i | 0 <= i && i <= maxUnsigned w -> pure (BV.mkBV w i)
           _ -> mzero

    FloatToSBV w r x ->
      do z <- floatToInteger r <$> f x
         case z of
           Just i | minSigned w <= i && i <= maxSigned w -> pure (BV.mkBV w i)
           _ -> mzero

    ------------------------------------------------------------------------
    -- Array Operations

    ArrayMap idx_types _ m def -> do
      m' <- traverse f (AUM.toMap m)
      h <- f def
      return $ case h of
        ArrayMapping h' -> ArrayMapping $ \idx ->
          case (`Map.lookup` m') =<< Ctx.zipWithM asIndexLit idx_types idx of
            Just r ->  return r
            Nothing -> h' idx
        ArrayConcrete d m'' ->
          -- Map.union is left-biased
          ArrayConcrete d (Map.union m' m'')

    ConstantArray _ _ v -> do
      val <- f v
      return $ ArrayConcrete val Map.empty

    SelectArray _ a i -> do
      arr <- f a
      let arrIdxTps = case exprType a of
                        BaseArrayRepr idx _ -> idx
      idx <- traverseFC (\e -> GVW <$> f e) i
      lift $ lookupArray arrIdxTps arr idx

    UpdateArray _ idx_tps a i v -> do
      arr <- f a
      idx <- traverseFC (\e -> GVW <$> f e) i
      v'  <- f v
      case arr of
        ArrayMapping arr' -> return . ArrayMapping $ \x ->
          if indicesEq idx_tps idx x then pure v' else arr' x
        ArrayConcrete d m -> do
          val <- f v
          let idx' = fromMaybe (error "UpdateArray only supported on Nat and BV") $ Ctx.zipWithM asIndexLit idx_tps idx
          return $ ArrayConcrete d (Map.insert idx' val m)

     where indicesEq :: Ctx.Assignment BaseTypeRepr ctx
                     -> Ctx.Assignment GroundValueWrapper ctx
                     -> Ctx.Assignment GroundValueWrapper ctx
                     -> Bool
           indicesEq tps x y =
             forallIndex (Ctx.size x) $ \j ->
               let GVW xj = x Ctx.! j
                   GVW yj = y Ctx.! j
                   tp = tps Ctx.! j
               in case tp of
                    BaseIntegerRepr -> xj == yj
                    BaseBVRepr _    -> xj == yj
                    _ -> error $ "We do not yet support UpdateArray on " ++ show tp ++ " indices."

    CopyArray{} -> error "CopyArray: unsupported."
    SetArray{} -> error "SetArray: unsupported."
    EqualArrayRange{} -> error "EqualArrayRange: unsupported."

    ------------------------------------------------------------------------
    -- Conversions

    IntegerToReal x -> toRational <$> f x
    BVToInteger x  -> BV.asUnsigned <$> f x
    SBVToInteger x -> BV.asSigned (bvWidth x) <$> f x

    RoundReal x -> roundAway <$> f x
    RoundEvenReal x -> round <$> f x
    FloorReal x -> floor <$> f x
    CeilReal  x -> ceiling <$> f x

    RealToInteger x -> floor <$> f x

    IntegerToBV x w -> BV.mkBV w <$> f x

    ------------------------------------------------------------------------
    -- Complex operations.

    Cplx (x :+ y) -> (:+) <$> f x <*> f y
    RealPart x -> realPart <$> f x
    ImagPart x -> imagPart <$> f x

    ------------------------------------------------------------------------
    -- String operations

    StringLength x -> stringLitLength <$> f x
    StringContains x y -> stringLitContains <$> f x <*> f y
    StringIsSuffixOf x y -> stringLitIsSuffixOf <$> f x <*> f y
    StringIsPrefixOf x y -> stringLitIsPrefixOf <$> f x <*> f y
    StringIndexOf x y k -> stringLitIndexOf <$> f x <*> f y <*> f k
    StringSubstring _ x off len -> stringLitSubstring <$> f x <*> f off <*> f len
    StringAppend si xs ->
      do let g x (SSeq.StringSeqLiteral l) = pure (x <> l)
             g x (SSeq.StringSeqTerm t)    = (x <>) <$> f t
         foldM g (stringLitEmpty si) (SSeq.toList xs)

    ------------------------------------------------------------------------
    -- Structs

    StructCtor _ flds -> do
      traverseFC (\v -> GVW <$> f v) flds
    StructField s i _ -> do
      sv <- f s
      return $! unGVW (sv Ctx.! i)
