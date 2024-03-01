{-|
Module      : What4.Expr.Builder
Description : Main definitions of the What4 expression representation
Copyright   : (c) Galois Inc, 2015-2020
License     : BSD3
Maintainer  : jhendrix@galois.com

This module defines the canonical implementation of the solver interface
from "What4.Interface". Type @'ExprBuilder' t st@ is
an instance of the classes 'IsExprBuilder' and 'IsSymExprBuilder'.

Notes regarding concurrency: The expression builder datatype contains
a number of mutable storage locations.  These are designed so they
may reasonably be used in a multithreaded context.  In particular,
nonce values are generated atomically, and other IORefs used in this
module are modified or written atomically, so modifications should
propagate in the expected sequentially-consistent ways.  Of course,
threads may still clobber state others have set (e.g., the current
program location) so the potential for truly multithreaded use is
somewhat limited.  Consider the @exprBuilderFreshConfig@ or
@exprBuilderSplitConfig@ operations if this is a concern.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.Builder
  ( -- * ExprBuilder
    ExprBuilder
  , newExprBuilder
  , getSymbolVarBimap
  , sbMakeExpr
  , sbNonceExpr
  , curProgramLoc
  , unaryThreshold
  , pushMuxOps
  , cacheStartSize
  , userState
  , exprCounter
  , startCaching
  , stopCaching
  , exprBuilderSplitConfig
  , exprBuilderFreshConfig

    -- * Specialized representations
  , bvUnary
  , intSum
  , realSum
  , bvSum
  , scalarMul

    -- * configuration options
  , unaryThresholdOption
  , cacheStartSizeOption
  , pushMuxOpsOption
  , cacheTerms

    -- * Expr
  , Expr(..)
  , asApp
  , asNonceApp
  , iteSize
  , exprLoc
  , ppExpr
  , ppExprTop
  , exprMaybeId
  , asConjunction
  , asDisjunction
  , Polarity(..)
  , BM.negatePolarity
    -- ** AppExpr
  , AppExpr
  , appExprId
  , appExprLoc
  , appExprApp
    -- ** NonceAppExpr
  , NonceAppExpr
  , nonceExprId
  , nonceExprLoc
  , nonceExprApp
    -- ** Type abbreviations
  , BoolExpr
  , IntegerExpr
  , RealExpr
  , FloatExpr
  , BVExpr
  , CplxExpr
  , StringExpr

    -- * App
  , App(..)
  , traverseApp
  , appType
    -- * NonceApp
  , NonceApp(..)
  , nonceAppType

    -- * Bound Variable information
  , ExprBoundVar
  , bvarId
  , bvarLoc
  , bvarName
  , bvarType
  , bvarKind
  , bvarAbstractValue
  , VarKind(..)
  , boundVars
  , ppBoundVar
  , evalBoundVars

    -- * Symbolic Function
  , ExprSymFn(..)
  , SymFnInfo(..)
  , symFnArgTypes
  , symFnReturnType
  , SomeExprSymFn(..)
  , ExprSymFnWrapper(..)

    -- * SymbolVarBimap
  , SymbolVarBimap
  , SymbolBinding(..)
  , emptySymbolVarBimap
  , lookupBindingOfSymbol
  , lookupSymbolOfBinding

    -- * IdxCache
  , IdxCache
  , newIdxCache
  , lookupIdx
  , lookupIdxValue
  , insertIdxValue
  , deleteIdxValue
  , clearIdxCache
  , idxCacheEval
  , idxCacheEval'

    -- * Flags
  , type FloatMode
  , FloatModeRepr(..)
  , FloatIEEE
  , FloatUninterpreted
  , FloatReal
  , Flags

    -- * BV Or Set
  , BVOrSet
  , bvOrToList
  , bvOrSingleton
  , bvOrInsert
  , bvOrUnion
  , bvOrAbs
  , traverseBVOrSet

    -- * Re-exports
  , SymExpr
  , What4.Interface.bvWidth
  , What4.Interface.exprType
  , What4.Interface.IndexLit(..)
  , What4.Interface.ArrayResultWrapper(..)
  ) where

import qualified Control.Exception as Ex
import           Control.Lens hiding (asIndex, (:>), Empty)
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.Trans.Writer.Strict (writer, runWriter)
import qualified Data.BitVector.Sized as BV
import           Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap

import           Data.Hashable
import qualified Data.HashTable.Class as HC
import qualified Data.HashTable.IO as H
import           Data.IORef
import           Data.Kind
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Monoid (Any(..))
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.HashTable as PH
import qualified Data.Parameterized.Map as PM
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Ratio (numerator, denominator)
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Float (castFloatToWord32, castDoubleToWord64)
import qualified LibBF as BF

import           What4.BaseTypes
import           What4.Concrete
import qualified What4.Config as CFG
import           What4.FloatMode
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.ProgramLoc
import qualified What4.SemiRing as SR
import qualified What4.SpecialFunctions as SFn
import           What4.Symbol

import           What4.Expr.Allocator
import           What4.Expr.App
import qualified What4.Expr.ArrayUpdateMap as AUM
import           What4.Expr.BoolMap (BoolMap, Polarity(..), BoolMapView(..))
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.MATLAB
import           What4.Expr.WeightedSum (WeightedSum, SemiRingProduct)
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.StringSeq as SSeq
import           What4.Expr.UnaryBV (UnaryBV)
import qualified What4.Expr.UnaryBV as UnaryBV
import qualified What4.Expr.VarIdentification as VI

import           What4.Utils.AbstractDomains
import           What4.Utils.Arithmetic
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex
import           What4.Utils.FloatHelpers
import           What4.Utils.StringLiteral

------------------------------------------------------------------------
-- Utilities

toDouble :: Rational -> Double
toDouble = fromRational

cachedEval :: (HashableF k, TestEquality k, MonadIO m)
           => PH.HashTable RealWorld k a
           -> k tp
           -> m (a tp)
           -> m (a tp)
cachedEval tbl k action = do
  mr <- liftIO $ stToIO $ PH.lookup tbl k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- action
      seq r $ do
      liftIO $ stToIO $ PH.insert tbl k r
      return r

------------------------------------------------------------------------
-- SymbolVarBimap

-- | A bijective map between vars and their canonical name for printing
-- purposes.
-- Parameter @t@ is a phantom type brand used to track nonces.
newtype SymbolVarBimap t = SymbolVarBimap (Bimap SolverSymbol (SymbolBinding t))

-- | This describes what a given SolverSymbol is associated with.
-- Parameter @t@ is a phantom type brand used to track nonces.
data SymbolBinding t
   = forall tp . VarSymbolBinding !(ExprBoundVar t tp)
     -- ^ Solver
   | forall args ret . FnSymbolBinding  !(ExprSymFn t args ret)

instance Eq (SymbolBinding t) where
  VarSymbolBinding x == VarSymbolBinding y = isJust (testEquality x y)
  FnSymbolBinding  x == FnSymbolBinding  y = isJust (testEquality (symFnId x) (symFnId y))
  _ == _ = False

instance Ord (SymbolBinding t) where
  compare (VarSymbolBinding x) (VarSymbolBinding y) =
    toOrdering (compareF x y)
  compare VarSymbolBinding{} _ = LT
  compare _ VarSymbolBinding{} = GT
  compare (FnSymbolBinding  x) (FnSymbolBinding  y) =
    toOrdering (compareF (symFnId x) (symFnId y))

-- | Empty symbol var bimap
emptySymbolVarBimap :: SymbolVarBimap t
emptySymbolVarBimap = SymbolVarBimap Bimap.empty

lookupBindingOfSymbol :: SolverSymbol -> SymbolVarBimap t -> Maybe (SymbolBinding t)
lookupBindingOfSymbol s (SymbolVarBimap m) = Bimap.lookup s m

lookupSymbolOfBinding :: SymbolBinding t -> SymbolVarBimap t -> Maybe SolverSymbol
lookupSymbolOfBinding b (SymbolVarBimap m) = Bimap.lookupR b m

------------------------------------------------------------------------
-- MatlabSolverFn

-- Parameter @t@ is a phantom type brand used to track nonces.
data MatlabFnWrapper t c where
   MatlabFnWrapper :: !(MatlabSolverFn (Expr t) a r) -> MatlabFnWrapper t (a::> r)

instance TestEquality (MatlabFnWrapper t) where
  testEquality (MatlabFnWrapper f) (MatlabFnWrapper g) = do
    Refl <- testSolverFnEq f g
    return Refl


instance HashableF (MatlabFnWrapper t) where
  hashWithSaltF s (MatlabFnWrapper f) = hashWithSalt s f

data ExprSymFnWrapper t c
   = forall a r . (c ~ (a ::> r)) => ExprSymFnWrapper (ExprSymFn t a r)

data SomeExprSymFn t = forall args ret . SomeExprSymFn (ExprSymFn t args ret)

instance Eq (SomeExprSymFn t) where
  (SomeExprSymFn fn1) == (SomeExprSymFn fn2) =
    isJust $ fnTestEquality fn1 fn2

instance Ord (SomeExprSymFn t) where
  compare (SomeExprSymFn fn1) (SomeExprSymFn fn2) =
    toOrdering $ fnCompare fn1 fn2

instance Hashable (SomeExprSymFn t) where
  hashWithSalt s (SomeExprSymFn fn) = hashWithSalt s fn

instance Show (SomeExprSymFn t) where
  show (SomeExprSymFn f) = show f


------------------------------------------------------------------------
-- ExprBuilder

data Flags (fi :: FloatMode)


-- | Cache for storing dag terms.
-- Parameter @t@ is a phantom type brand used to track nonces.
data ExprBuilder t (st :: Type -> Type) (fs :: Type)
   = forall fm. (fs ~ (Flags fm)) =>
     SB { sbTrue  :: !(BoolExpr t)
        , sbFalse :: !(BoolExpr t)

          -- | Constant zero.
        , sbZero  :: !(RealExpr t)

          -- | Configuration object for this symbolic backend
        , sbConfiguration :: !CFG.Config

          -- | Flag used to tell the backend whether to evaluate
          -- ground rational values as double precision floats when
          -- a function cannot be evaluated as a rational.
        , sbFloatReduce :: !Bool

          -- | The maximum number of distinct values a term may have and use the
          -- unary representation.
        , sbUnaryThreshold :: !(CFG.OptionSetting BaseIntegerType)

          -- | The starting size when building a new cache
        , sbCacheStartSize :: !(CFG.OptionSetting BaseIntegerType)

          -- | If enabled, push certain 'ExprBuilder' operations (e.g., @zext@)
          -- down to the branches of @ite@ expressions. In some (but not all)
          -- circumstances, this can result in operations that are easier for
          -- SMT solvers to reason about.
        , sbPushMuxOps :: !(CFG.OptionSetting BaseBoolType)

          -- | Counter to generate new unique identifiers for elements and functions.
        , sbExprCounter :: !(NonceGenerator IO t)

          -- | Reference to current allocator for expressions.
        , sbCurAllocator :: !(IORef (ExprAllocator t))

          -- | Number of times an 'Expr' for a non-linear operation has been
          -- created.
        , sbNonLinearOps :: !(IORef Integer)

          -- | The current program location
        , sbProgramLoc :: !(IORef ProgramLoc)

          -- | User-provided state
        , sbUserState :: !(st t)

        , sbVarBindings :: !(IORef (SymbolVarBimap t))

        , sbUninterpFnCache :: !(IORef (Map (SolverSymbol, Some (Ctx.Assignment BaseTypeRepr)) (SomeSymFn (ExprBuilder t st fs))))

          -- | Cache for Matlab functions
        , sbMatlabFnCache :: !(PH.HashTable RealWorld (MatlabFnWrapper t) (ExprSymFnWrapper t))

        , sbSolverLogger :: !(IORef (Maybe (SolverEvent -> IO ())))

          -- | Flag dictating how floating-point values/operations are translated
          -- when passed to the solver.
        , sbFloatMode :: !(FloatModeRepr fm)
        }

type instance SymFn (ExprBuilder t st fs) = ExprSymFn t
type instance SymExpr (ExprBuilder t st fs) = Expr t
type instance BoundVar (ExprBuilder t st fs) = ExprBoundVar t
type instance SymAnnotation (ExprBuilder t st fs) = Nonce t

exprCounter :: Getter (ExprBuilder t st fs) (NonceGenerator IO t)
exprCounter = to sbExprCounter

userState :: Lens' (ExprBuilder t st fs) (st t)
userState = lens sbUserState (\sym st -> sym{ sbUserState = st })

unaryThreshold :: Getter (ExprBuilder t st fs) (CFG.OptionSetting BaseIntegerType)
unaryThreshold = to sbUnaryThreshold

cacheStartSize :: Getter (ExprBuilder t st fs) (CFG.OptionSetting BaseIntegerType)
cacheStartSize = to sbCacheStartSize

pushMuxOps :: Getter (ExprBuilder t st fs) (CFG.OptionSetting BaseBoolType)
pushMuxOps = to sbPushMuxOps

-- | Return a new expr builder where the configuration object has
--   been "split" using the @splitConfig@ operation.
--   The returned sym will share any preexisting options with the
--   input sym, but any new options added with @extendConfig@
--   will not be shared. This may be useful if the expression builder
--   needs to be shared across threads, or sequentially for
--   separate use cases.  Note, however, that hash consing settings,
--   solver loggers and the current program location will be shared.
exprBuilderSplitConfig :: ExprBuilder t st fs -> IO (ExprBuilder t st fs)
exprBuilderSplitConfig sym =
  do cfg' <- CFG.splitConfig (sbConfiguration sym)
     return sym{ sbConfiguration = cfg' }


-- | Return a new expr builder where all configuration settings have
--   been isolated from the original. The @Config@ object of the
--   output expr builder will have only the default options that are
--   installed via @newExprBuilder@, and configuration changes
--   to either expr builder will not be visible to the other.
--   This includes caching settings, the current program location,
--   and installed solver loggers.
exprBuilderFreshConfig :: ExprBuilder t st fs -> IO (ExprBuilder t st fs)
exprBuilderFreshConfig sym =
  do let gen = sbExprCounter sym
     es <- newStorage gen

     loc_ref       <- newIORef initializationLoc
     storage_ref   <- newIORef es
     logger_ref    <- newIORef Nothing
     bindings_ref  <- newIORef =<< readIORef (sbVarBindings sym)

     -- Set up configuration options
     cfg <- CFG.initialConfig 0
              [ unaryThresholdDesc
              , cacheStartSizeDesc
              , pushMuxOpsDesc
              ]
     unarySetting       <- CFG.getOptionSetting unaryThresholdOption cfg
     cacheStartSetting  <- CFG.getOptionSetting cacheStartSizeOption cfg
     pushMuxOpsStartSetting <- CFG.getOptionSetting pushMuxOpsOption cfg
     CFG.extendConfig [cacheOptDesc gen storage_ref cacheStartSetting] cfg
     nonLinearOps <- newIORef 0

     return sym { sbConfiguration = cfg
                , sbFloatReduce = True
                , sbUnaryThreshold = unarySetting
                , sbCacheStartSize = cacheStartSetting
                , sbPushMuxOps = pushMuxOpsStartSetting
                , sbProgramLoc = loc_ref
                , sbCurAllocator = storage_ref
                , sbNonLinearOps = nonLinearOps
                , sbVarBindings = bindings_ref
                , sbSolverLogger = logger_ref
                }

------------------------------------------------------------------------
-- IdxCache

-- | An IdxCache is used to map expressions with type @Expr t tp@ to
-- values with a corresponding type @f tp@. It is a mutable map using
-- an 'IO' hash table. Parameter @t@ is a phantom type brand used to
-- track nonces.
newtype IdxCache t (f :: BaseType -> Type)
      = IdxCache { cMap :: IORef (PM.MapF (Nonce t) f) }

-- | Create a new IdxCache
newIdxCache :: MonadIO m => m (IdxCache t f)
newIdxCache = liftIO $ IdxCache <$> newIORef PM.empty

{-# INLINE lookupIdxValue #-}
-- | Return the value associated to the expr in the index.
lookupIdxValue :: MonadIO m => IdxCache t f -> Expr t tp -> m (Maybe (f tp))
lookupIdxValue _ SemiRingLiteral{} = return Nothing
lookupIdxValue _ StringExpr{} = return Nothing
lookupIdxValue _ BoolExpr{} = return Nothing
lookupIdxValue _ FloatExpr{} = return Nothing
lookupIdxValue c (NonceAppExpr e) = lookupIdx c (nonceExprId e)
lookupIdxValue c (AppExpr e)  = lookupIdx c (appExprId e)
lookupIdxValue c (BoundVarExpr i) = lookupIdx c (bvarId i)

{-# INLINE lookupIdx #-}
lookupIdx :: (MonadIO m) => IdxCache t f -> Nonce t tp -> m (Maybe (f tp))
lookupIdx c n = liftIO $ PM.lookup n <$> readIORef (cMap c)

{-# INLINE insertIdxValue #-}
-- | Bind the value to the given expr in the index.
insertIdxValue :: MonadIO m => IdxCache t f -> Nonce t tp -> f tp -> m ()
insertIdxValue c e v = seq v $ liftIO $ atomicModifyIORef' (cMap c) $ (\m -> (PM.insert e v m, ()))

{-# INLINE deleteIdxValue #-}
-- | Remove a value from the IdxCache
deleteIdxValue :: MonadIO m => IdxCache t f -> Nonce t (tp :: BaseType) -> m ()
deleteIdxValue c e = liftIO $ atomicModifyIORef' (cMap c) $ (\m -> (PM.delete e m, ()))

-- | Remove all values from the IdxCache
clearIdxCache :: MonadIO m => IdxCache t f -> m ()
clearIdxCache c = liftIO $ atomicWriteIORef (cMap c) PM.empty

exprMaybeId :: Expr t tp -> Maybe (Nonce t tp)
exprMaybeId SemiRingLiteral{} = Nothing
exprMaybeId StringExpr{} = Nothing
exprMaybeId BoolExpr{} = Nothing
exprMaybeId FloatExpr{} = Nothing
exprMaybeId (NonceAppExpr e) = Just $! nonceExprId e
exprMaybeId (AppExpr  e) = Just $! appExprId e
exprMaybeId (BoundVarExpr e) = Just $! bvarId e

-- | Implements a cached evaluated using the given element.  Given an element
-- this function returns the value of the element if bound, and otherwise
-- calls the evaluation function, stores the result in the cache, and
-- returns the value.
{-# INLINE idxCacheEval #-}
idxCacheEval :: (MonadIO m)
             => IdxCache t f
             -> Expr t tp
             -> m (f tp)
             -> m (f tp)
idxCacheEval c e m = do
  case exprMaybeId e of
    Nothing -> m
    Just n -> idxCacheEval' c n m

-- | Implements a cached evaluated using the given element.  Given an element
-- this function returns the value of the element if bound, and otherwise
-- calls the evaluation function, stores the result in the cache, and
-- returns the value.
{-# INLINE idxCacheEval' #-}
idxCacheEval' :: (MonadIO m)
              => IdxCache t f
              -> Nonce t tp
              -> m (f tp)
              -> m (f tp)
idxCacheEval' c n m = do
  mr <- lookupIdx c n
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      insertIdxValue c n r
      return r

------------------------------------------------------------------------
-- ExprBuilder operations

curProgramLoc :: ExprBuilder t st fs -> IO ProgramLoc
curProgramLoc sym = readIORef (sbProgramLoc sym)

-- | Create an element from a nonce app.
sbNonceExpr :: ExprBuilder t st fs
           -> NonceApp t (Expr t) tp
           -> IO (Expr t tp)
sbNonceExpr sym a = do
  s <- readIORef (sbCurAllocator sym)
  pc <- curProgramLoc sym
  nonceExpr s pc a (quantAbsEval exprAbsValue a)

semiRingLit :: ExprBuilder t st fs
            -> SR.SemiRingRepr sr
            -> SR.Coefficient sr
            -> IO (Expr t (SR.SemiRingBase sr))
semiRingLit sb sr x = do
  l <- curProgramLoc sb
  return $! SemiRingLiteral sr x l

sbMakeExpr :: ExprBuilder t st fs -> App (Expr t) tp -> IO (Expr t tp)
sbMakeExpr sym a = do
  s <- readIORef (sbCurAllocator sym)
  pc <- curProgramLoc sym
  let v = abstractEval exprAbsValue a
  when (isNonLinearApp a) $
    atomicModifyIORef' (sbNonLinearOps sym) (\n -> (n+1,()))
  case appType a of
    -- Check if abstract interpretation concludes this is a constant.
    BaseBoolRepr | Just b <- v -> return $ backendPred sym b
    BaseIntegerRepr | Just c <- asSingleRange v -> intLit sym c
    BaseRealRepr | Just c <- asSingleRange (ravRange v) -> realLit sym c
    BaseBVRepr w | Just x <- BVD.asSingleton v -> bvLit sym w (BV.mkBV w x)
    _ -> appExpr s pc a v

-- | Update the binding to point to the current variable.
updateVarBinding :: ExprBuilder t st fs
                 -> SolverSymbol
                 -> SymbolBinding t
                 -> IO ()
updateVarBinding sym nm v
  | nm == emptySymbol = return ()
  | otherwise =
    atomicModifyIORef' (sbVarBindings sym) $ (\x -> v `seq` (ins nm v x, ()))
  where ins n x (SymbolVarBimap m) = SymbolVarBimap (Bimap.insert n x m)

-- | Creates a new bound var.
sbMakeBoundVar :: ExprBuilder t st fs
               -> SolverSymbol
               -> BaseTypeRepr tp
               -> VarKind
               -> Maybe (AbstractValue tp)
               -> IO (ExprBoundVar t tp)
sbMakeBoundVar sym nm tp k absVal = do
  n  <- sbFreshIndex sym
  pc <- curProgramLoc sym
  return $! BVar { bvarId   = n
                 , bvarLoc  = pc
                 , bvarName = nm
                 , bvarType = tp
                 , bvarKind = k
                 , bvarAbstractValue = absVal
                 }

-- | Create fresh index
sbFreshIndex :: ExprBuilder t st fs -> IO (Nonce t (tp::BaseType))
sbFreshIndex sb = freshNonce (sbExprCounter sb)

sbFreshSymFnNonce :: ExprBuilder t st fs -> IO (Nonce t (ctx:: Ctx BaseType))
sbFreshSymFnNonce sb = freshNonce (sbExprCounter sb)

------------------------------------------------------------------------
-- Configuration option for controlling the maximum number of value a unary
-- threshold may have.

-- | Maximum number of values in unary bitvector encoding.
--
--   This option is named \"backend.unary_threshold\"
unaryThresholdOption :: CFG.ConfigOption BaseIntegerType
unaryThresholdOption = CFG.configOption BaseIntegerRepr "backend.unary_threshold"

-- | The configuration option for setting the maximum number of
-- values a unary threshold may have.
unaryThresholdDesc :: CFG.ConfigDesc
unaryThresholdDesc = CFG.mkOpt unaryThresholdOption sty help (Just (ConcreteInteger 0))
  where sty = CFG.integerWithMinOptSty (CFG.Inclusive 0)
        help = Just "Maximum number of values in unary bitvector encoding."

------------------------------------------------------------------------
-- Configuration option for controlling whether to push certain ExprBuilder
-- operations (e.g., @zext@) down to the branches of @ite@ expressions.

-- | TODO RGS: Docs
pushMuxOpsOption :: CFG.ConfigOption BaseBoolType
pushMuxOpsOption = CFG.configOption BaseBoolRepr "backend.push_mux_ops"

-- | TODO RGS: Docs
pushMuxOpsDesc :: CFG.ConfigDesc
pushMuxOpsDesc = CFG.mkOpt pushMuxOpsOption sty help (Just (ConcreteBool False))
  where sty = CFG.boolOptSty
        help = Just "Maximum number of values in unary bitvector encoding."


newExprBuilder ::
  FloatModeRepr fm
  -- ^ Float interpretation mode (i.e., how are floats translated for the solver).
  -> st t
  -- ^ Initial state for the expression builder
  -> NonceGenerator IO t
  -- ^ Nonce generator for names
  ->  IO (ExprBuilder t st (Flags fm))
newExprBuilder floatMode st gen = do
  es <- newStorage gen

  let t = BoolExpr True initializationLoc
  let f = BoolExpr False initializationLoc
  let z = SemiRingLiteral SR.SemiRingRealRepr 0 initializationLoc

  loc_ref       <- newIORef initializationLoc
  storage_ref   <- newIORef es
  bindings_ref  <- newIORef emptySymbolVarBimap
  uninterp_fn_cache_ref <- newIORef Map.empty
  matlabFnCache <- stToIO $ PH.new
  loggerRef     <- newIORef Nothing

  -- Set up configuration options
  cfg <- CFG.initialConfig 0
           [ unaryThresholdDesc
           , cacheStartSizeDesc
           , pushMuxOpsDesc
           ]
  unarySetting       <- CFG.getOptionSetting unaryThresholdOption cfg
  cacheStartSetting  <- CFG.getOptionSetting cacheStartSizeOption cfg
  pushMuxOpsStartSetting <- CFG.getOptionSetting pushMuxOpsOption cfg
  CFG.extendConfig [cacheOptDesc gen storage_ref cacheStartSetting] cfg
  nonLinearOps <- newIORef 0

  return $! SB { sbTrue  = t
               , sbFalse = f
               , sbZero = z
               , sbConfiguration = cfg
               , sbFloatReduce = True
               , sbUnaryThreshold = unarySetting
               , sbCacheStartSize = cacheStartSetting
               , sbPushMuxOps = pushMuxOpsStartSetting
               , sbProgramLoc = loc_ref
               , sbExprCounter = gen
               , sbCurAllocator = storage_ref
               , sbNonLinearOps = nonLinearOps
               , sbUserState = st
               , sbVarBindings = bindings_ref
               , sbUninterpFnCache = uninterp_fn_cache_ref
               , sbMatlabFnCache = matlabFnCache
               , sbSolverLogger = loggerRef
               , sbFloatMode = floatMode
               }

-- | Get current variable bindings.
getSymbolVarBimap :: ExprBuilder t st fs -> IO (SymbolVarBimap t)
getSymbolVarBimap sym = readIORef (sbVarBindings sym)

-- | Stop caching applications in backend.
stopCaching :: ExprBuilder t st fs -> IO ()
stopCaching sb = do
  s <- newStorage (sbExprCounter sb)
  atomicWriteIORef (sbCurAllocator sb) s

-- | Restart caching applications in backend (clears cache if it is currently caching).
startCaching :: ExprBuilder t st fs -> IO ()
startCaching sb = do
  sz <- CFG.getOpt (sbCacheStartSize sb)
  s <- newCachedStorage (sbExprCounter sb) (fromInteger sz)
  atomicWriteIORef (sbCurAllocator sb) s

bvBinDivOp :: (1 <= w)
            => (NatRepr w -> BV.BV w -> BV.BV w -> BV.BV w)
            -> (NatRepr w -> BVExpr t w -> BVExpr t w -> App (Expr t) (BaseBVType w))
            -> ExprBuilder t st fs
            -> BVExpr t w
            -> BVExpr t w
            -> IO (BVExpr t w)
bvBinDivOp f c sb x y = do
  let w = bvWidth x
  case (asBV x, asBV y) of
    (Just i, Just j) | j /= BV.zero w -> bvLit sb w $ f w i j
    _ -> sbMakeExpr sb $ c w x y

asConcreteIndices :: IsExpr e
                  => Ctx.Assignment e ctx
                  -> Maybe (Ctx.Assignment IndexLit ctx)
asConcreteIndices = traverseFC f
  where f :: IsExpr e => e tp -> Maybe (IndexLit tp)
        f x =
          case exprType x of
            BaseIntegerRepr  -> IntIndexLit <$> asInteger x
            BaseBVRepr w -> BVIndexLit w <$> asBV x
            _ -> Nothing

symbolicIndices :: forall sym ctx
                 . IsExprBuilder sym
                => sym
                -> Ctx.Assignment IndexLit ctx
                -> IO (Ctx.Assignment (SymExpr sym) ctx)
symbolicIndices sym = traverseFC f
  where f :: IndexLit tp -> IO (SymExpr sym tp)
        f (IntIndexLit n)  = intLit sym n
        f (BVIndexLit w i) = bvLit sym w i

-- | This evaluate a symbolic function against a set of arguments.
betaReduce :: ExprBuilder t st fs
           -> ExprSymFn t args ret
           -> Ctx.Assignment (Expr t) args
           -> IO (Expr t ret)
betaReduce sym f args =
  case symFnInfo f of
    UninterpFnInfo{} ->
      sbNonceExpr sym $! FnApp f args
    DefinedFnInfo bound_vars e _ -> do
      evalBoundVars sym e bound_vars args
    MatlabSolverFnInfo fn_id _ _ -> do
      evalMatlabSolverFn fn_id sym args

-- | This runs one action, and if it returns a value different from the input,
-- then it runs the second.  Otherwise it returns the result value passed in.
--
-- It is used when an action may modify a value, and we only want to run a
-- second action if the value changed.
runIfChanged :: (Eq e, Monad m)
             => e
             -> (e -> m e) -- ^ First action to run
             -> r           -- ^ Result if no change.
             -> (e -> m r) -- ^ Second action to run
             -> m r
runIfChanged x f unChanged onChange = do
  y <- f x
  if x == y then
    return unChanged
   else
    onChange y

-- | This adds a binding from the variable to itself in the hashtable
-- to ensure it can't be rebound.
recordBoundVar :: PH.HashTable RealWorld (Expr t) (Expr t)
                  -> ExprBoundVar t tp
                  -> IO ()
recordBoundVar tbl v = do
  let e = BoundVarExpr v
  mr <- stToIO $ PH.lookup tbl e
  case mr of
    Just r -> do
      when (r /= e) $ do
        fail $ "Simulator internal error; do not support rebinding variables."
    Nothing -> do
      -- Bind variable to itself to ensure we catch when it is used again.
      stToIO $ PH.insert tbl e e


-- | The CachedSymFn is used during evaluation to store the results of reducing
-- the definitions of symbolic functions.
--
-- For each function it stores a pair containing a 'Bool' that is true if the
-- function changed as a result of evaluating it, and the reduced function
-- after evaluation.
--
-- The second arguments contains the arguments with the return type appended.
data CachedSymFn t c
  = forall a r
    . (c ~ (a ::> r))
    => CachedSymFn Bool (ExprSymFn t a r)

-- | Data structure used for caching evaluation.
data EvalHashTables t
   = EvalHashTables { exprTable :: !(PH.HashTable RealWorld (Expr t) (Expr t))
                    , fnTable  :: !(PH.HashTable RealWorld (Nonce t) (CachedSymFn t))
                    }

-- | Evaluate a simple function.
--
-- This returns whether the function changed as a Boolean and the function itself.
evalSimpleFn :: EvalHashTables t
             -> ExprBuilder t st fs
             -> ExprSymFn t idx ret
             -> IO (Bool,ExprSymFn t idx ret)
evalSimpleFn tbl sym f = do
  let n = symFnId f
  case symFnInfo f of
    UninterpFnInfo{} -> do
      CachedSymFn changed f' <- cachedEval (fnTable tbl) n $
        return $! CachedSymFn False f
      return (changed, f')
    DefinedFnInfo vars e evalFn -> do
      let nm = symFnName f
      CachedSymFn changed f' <-
        cachedEval (fnTable tbl) n $ do
          traverseFC_ (recordBoundVar (exprTable tbl)) vars
          e' <- evalBoundVars' tbl sym e
          if e == e' then
            return $! CachedSymFn False f
           else
            CachedSymFn True <$> definedFn sym nm vars e' evalFn
      return (changed, f')
    MatlabSolverFnInfo{} -> return (False, f)

evalBoundVars' :: forall t st fs ret
               .  EvalHashTables t
               -> ExprBuilder t st fs
               -> Expr t ret
               -> IO (Expr t ret)
evalBoundVars' tbls sym e0 =
  case e0 of
    SemiRingLiteral{} -> return e0
    StringExpr{} -> return e0
    BoolExpr{} -> return e0
    FloatExpr{} -> return e0
    AppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      let a = appExprApp ae
      a' <- traverseApp (evalBoundVars' tbls sym) a
      if a == a' then
        return e0
       else
        reduceApp sym bvUnary a'
    NonceAppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      case nonceExprApp ae of
        Annotation tpr n a -> do
          a' <- evalBoundVars' tbls sym a
          if a == a' then
            return e0
          else
            sbNonceExpr sym $ Annotation tpr n a'
        Forall v e -> do
          recordBoundVar (exprTable tbls) v
          -- Regenerate forallPred if e is changed by evaluation.
          runIfChanged e (evalBoundVars' tbls sym) e0 (forallPred sym v)
        Exists v e -> do
          recordBoundVar (exprTable tbls) v
          -- Regenerate forallPred if e is changed by evaluation.
          runIfChanged e (evalBoundVars' tbls sym) e0 (existsPred sym v)
        ArrayFromFn f -> do
          (changed, f') <- evalSimpleFn tbls sym f
          if not changed then
            return e0
           else
            arrayFromFn sym f'
        MapOverArrays f _ args -> do
          (changed, f') <- evalSimpleFn tbls sym f
          let evalWrapper :: ArrayResultWrapper (Expr t) (idx ::> itp) utp
                          -> IO (ArrayResultWrapper (Expr t) (idx ::> itp) utp)
              evalWrapper (ArrayResultWrapper a) =
                ArrayResultWrapper <$> evalBoundVars' tbls sym a
          args' <- traverseFC evalWrapper args
          if not changed && args == args' then
            return e0
           else
            arrayMap sym f' args'
        ArrayTrueOnEntries f a -> do
          (changed, f') <- evalSimpleFn tbls sym f
          a' <- evalBoundVars' tbls sym a
          if not changed && a == a' then
            return e0
           else
            arrayTrueOnEntries sym f' a'
        FnApp f a -> do
          (changed, f') <- evalSimpleFn tbls sym f
          a' <- traverseFC (evalBoundVars' tbls sym) a
          if not changed && a == a' then
            return e0
           else
            applySymFn sym f' a'

    BoundVarExpr{} -> cachedEval (exprTable tbls) e0 $ return e0

initHashTable :: (HashableF key, TestEquality key)
              => Ctx.Assignment key args
              -> Ctx.Assignment val args
              -> ST s (PH.HashTable s key val)
initHashTable keys vals = do
  let sz = Ctx.size keys
  tbl <- PH.newSized (Ctx.sizeInt sz)
  Ctx.forIndexM sz $ \i -> do
    PH.insert tbl (keys Ctx.! i) (vals Ctx.! i)
  return tbl

-- | This evaluates the term with the given bound variables rebound to
-- the given arguments.
--
-- The algorithm works by traversing the subterms in the term in a bottom-up
-- fashion while using a hash-table to memoize results for shared subterms.  The
-- hash-table is pre-populated so that the bound variables map to the element,
-- so we do not need any extra map lookup when checking to see if a variable is
-- bound.
--
-- NOTE: This function assumes that variables in the substitution are not
-- themselves bound in the term (e.g. in a function definition or quantifier).
-- If this is not respected, then 'evalBoundVars' will call 'fail' with an
-- error message.
evalBoundVars :: ExprBuilder t st fs
              -> Expr t ret
              -> Ctx.Assignment (ExprBoundVar t) args
              -> Ctx.Assignment (Expr t) args
              -> IO (Expr t ret)
evalBoundVars sym e vars exprs = do
  expr_tbl <- stToIO $ initHashTable (fmapFC BoundVarExpr vars) exprs
  fn_tbl  <- stToIO $ PH.new
  let tbls = EvalHashTables { exprTable = expr_tbl
                            , fnTable  = fn_tbl
                            }
  evalBoundVars' tbls sym e


-- | `ExprTransformer` and the associated code implement bidirectional bitvector
-- (BV) to/from linear integer arithmetic (LIA) transformations. This is done by
-- replacing all BV operations with LIA operations, replacing all BV variables
-- with LIA variables, and by replacing all BV function symbols with LIA
-- function symbols. The reverse transformation works the same way, but in
-- reverse. This transformation is not sound, but in practice it is useful.
--
-- This is used to implement `transformPredBV2LIA` and `transformSymFnLIA2BV`,
-- which in turn are used to implement @runZ3Horn@.
--
-- This is highly experimental and may be unstable.
newtype ExprTransformer t (tp1 :: BaseType) (tp2 :: BaseType) a =
  ExprTransformer (ExceptT String (ReaderT (ExprTransformerTables t tp1 tp2) IO) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader (ExprTransformerTables t tp1 tp2), MonadError String)

data ExprTransformerTables t (tp1 :: BaseType) (tp2 :: BaseType) = ExprTransformerTables
  { evalTables :: !(EvalHashTables t)
  , transformerSubst :: !(H.BasicHashTable (ExprBoundVar t tp1) (ExprBoundVar t tp2))
  , transformerFnSubst :: !(H.BasicHashTable (SomeExprSymFn t) (SomeExprSymFn t))
  }

runExprTransformer :: ExprTransformer t tp1 tp2 a -> ExprTransformerTables t tp1 tp2 -> IO (Either String a)
runExprTransformer (ExprTransformer action) = runReaderT (runExceptT action)

type BV2LIAExprTransformer t = ExprTransformer t (BaseBVType 64) BaseIntegerType
type LIA2BVExprTransformer t = ExprTransformer t BaseIntegerType (BaseBVType 64)
type HasTransformerConstraints t st fs tp1 tp2 =
  ( KnownRepr BaseTypeRepr tp1
  , KnownRepr BaseTypeRepr tp2
  , ?transformCmpTp1ToTp2 :: ExprBuilder t st fs -> Expr t BaseBoolType -> Maybe (ExprTransformer t tp1 tp2 (Expr t BaseBoolType))
  , ?transformExprTp1ToTp2 :: ExprBuilder t st fs -> Expr t tp1 -> ExprTransformer t tp1 tp2 (Expr t tp2)
  )

transformPred ::
  forall t st fs tp1 tp2 .
  HasTransformerConstraints t st fs tp1 tp2 =>
  ExprBuilder t st fs ->
  Expr t BaseBoolType ->
  ExprTransformer t tp1 tp2 (Expr t BaseBoolType)
transformPred sym e0 = exprTransformerCachedEval e0 $ case e0 of
  _ | Just action <- ?transformCmpTp1ToTp2 sym e0 -> action

  BoolExpr{} -> return e0

  AppExpr ae -> do
    let a = appExprApp ae
    a' <- traverseApp
      (\a'' -> case testEquality BaseBoolRepr (exprType a'') of
        Just Refl -> transformPred sym a''
        Nothing -> throwError $ "transformPred: unsupported non-boolean expression " ++ show a'')
      a
    if a == a' then
      return e0
    else
      liftIO $ reduceApp sym bvUnary a'

  NonceAppExpr ae -> do
    case nonceExprApp ae of
      Annotation tpr n a -> do
        a' <- transformPred sym a
        if a == a' then
          return e0
        else
          liftIO $ sbNonceExpr sym $ Annotation tpr n a'
      Forall v e -> do
        quantifier <- transformVarTp1ToTp2WithCont sym v (forallPred sym)
        -- Regenerate forallPred if e is changed by evaluation.
        runIfChanged e (transformPred sym) e0 $ liftIO . quantifier
      Exists v e -> do
        quantifier <- transformVarTp1ToTp2WithCont sym v (existsPred sym)
        -- Regenerate existsPred if e is changed by evaluation.
        runIfChanged e (transformPred sym) e0 $ liftIO . quantifier
      FnApp f a -> do
        (SomeExprSymFn f') <- transformFn sym $ SomeExprSymFn f
        (Some a') <- Ctx.fromList <$> mapM
          (\(Some a'') ->
            applyTp1ToTp2FunWithCont (?transformExprTp1ToTp2 sym) (transformPred sym) Some (exprType a'') a'')
          (toListFC Some a)
        case testEquality ((fmapFC exprType a') :> (fnReturnType f)) ((fnArgTypes f') :> (fnReturnType f')) of
          Just Refl -> liftIO $ applySymFn sym f' a'
          Nothing -> throwError $ "transformPred: unsupported FnApp " ++ show e0
      _ -> throwError $ "transformPred: unsupported NonceAppExpr " ++ show e0

  BoundVarExpr{} -> return e0

transformFn ::
  forall t st fs tp1 tp2 .
  HasTransformerConstraints t st fs tp1 tp2 =>
  ExprBuilder t st fs ->
  SomeExprSymFn t ->
  ExprTransformer t tp1 tp2 (SomeExprSymFn t)
transformFn sym (SomeExprSymFn f) = do
  inv_subst <- asks transformerFnSubst
  case symFnInfo f of
    UninterpFnInfo{}
      | Just Refl <- testEquality BaseBoolRepr (fnReturnType f) -> do
        (Some tps) <- Ctx.fromList <$> mapM
          (\(Some tp) -> applyTp1ToTp2FunWithCont (\_ -> return knownRepr) return Some tp tp)
          (toListFC Some $ fnArgTypes f)
        liftIO $ mutateInsertIO inv_subst (SomeExprSymFn f) $
          SomeExprSymFn <$> freshTotalUninterpFn sym (symFnName f) tps BaseBoolRepr
      | otherwise -> throwError $ "transformFn: unsupported UninterpFnInfo " ++ show f

    DefinedFnInfo vars e eval_fn
      | Just Refl <- testEquality BaseBoolRepr (fnReturnType f) -> do
        (Some vars') <- Ctx.fromList <$>
          mapM (\(Some v) -> transformVarTp1ToTp2WithCont sym v Some) (toListFC Some vars)
        e' <- transformPred sym e
        liftIO $ mutateInsertIO inv_subst (SomeExprSymFn f) $
          SomeExprSymFn <$> definedFn sym (symFnName f) vars' e' eval_fn
      | otherwise -> throwError $ "transformFn: unsupported DefinedFnInfo " ++ show f

    MatlabSolverFnInfo{} -> throwError $ "transformFn: unsupported MatlabSolverFnInfo " ++ show f

exprTransformerCachedEval ::
  Expr t tp -> ExprTransformer t tp1 tp2 (Expr t tp) -> ExprTransformer t tp1 tp2 (Expr t tp)
exprTransformerCachedEval e action = do
  tbls <- asks evalTables
  cachedEval (exprTable tbls) e action

transformCmpBV2LIA ::
  ExprBuilder t st fs ->
  Expr t BaseBoolType ->
  Maybe (BV2LIAExprTransformer t (Expr t BaseBoolType))
transformCmpBV2LIA sym e
  | Just (BaseEq _ x y) <- asApp e
  , Just Refl <- testEquality (BaseBVRepr $ knownNat @64) (exprType x) = Just $ do
    x' <- transformExprBV2LIA sym x
    y' <- transformExprBV2LIA sym y
    liftIO $ intEq sym x' y'

  | Just (BVUlt x y) <- asApp e
  , Just Refl <- testEquality (BaseBVRepr $ knownNat @64) (exprType x) = Just $ do
    x' <- transformExprBV2LIA sym x
    y' <- transformExprBV2LIA sym y
    liftIO $ intLt sym x' y'

  | Just (BVSlt x y) <- asApp e
  , Just Refl <- testEquality (BaseBVRepr $ knownNat @64) (exprType x) = Just $ do
    x' <- transformExprBV2LIA sym x
    y' <- transformExprBV2LIA sym y
    liftIO $ intLt sym x' y'

  | otherwise = Nothing

transformExprBV2LIA ::
  ExprBuilder t st fs ->
  Expr t (BaseBVType 64) ->
  BV2LIAExprTransformer t (Expr t BaseIntegerType)
transformExprBV2LIA sym e
  | Just semi_ring_sum <- asSemiRingSum (SR.SemiRingBVRepr SR.BVArithRepr (bvWidth e)) e =
    liftIO . semiRingSum sym =<<
      WSum.transformSum
        SR.SemiRingIntegerRepr
        (return . BV.asSigned (bvWidth e))
        (transformExprBV2LIA sym)
        semi_ring_sum

  | Just semi_ring_prod <- asSemiRingProd (SR.SemiRingBVRepr SR.BVArithRepr (bvWidth e)) e
  , Just e' <- WSum.asProdVar semi_ring_prod =
    transformExprBV2LIA sym e'

  | Just semi_ring_sum <- asSemiRingSum (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth e)) e
  , Just e' <- WSum.asVar semi_ring_sum =
    transformExprBV2LIA sym e'

  | Just semi_ring_prod <- asSemiRingProd (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth e)) e
  , Just e' <- WSum.asProdVar semi_ring_prod =
    transformExprBV2LIA sym e'

  | Just semi_ring_sum <- asSemiRingSum (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth e)) e
  , Just (c', e') <- WSum.asWeightedVar semi_ring_sum
  , Just semi_ring_sum' <- asSemiRingSum (SR.SemiRingBVRepr SR.BVArithRepr (bvWidth e')) e'
  , Just (c'', e'') <- WSum.asWeightedVar semi_ring_sum'
  , Just (BaseIte _ _ c a b) <- asApp e''
  , Just a_bv <- asBV a
  , Just b_bv <- asBV b = do
    x <- liftIO $ bvLit sym (bvWidth e) $ BV.xor c' $ BV.mul (bvWidth e) c'' a_bv
    y <- liftIO $ bvLit sym (bvWidth e) $ BV.xor c' $ BV.mul (bvWidth e) c'' b_bv
    transformExprBV2LIA sym =<< liftIO (bvIte sym c x y)

  | BoundVarExpr v <- e =
    BoundVarExpr <$> transformVarTp1ToTp2 sym v

  | Just (BaseIte _ _ c x y) <- asApp e = do
    let ?transformCmpTp1ToTp2 = transformCmpBV2LIA
        ?transformExprTp1ToTp2 = transformExprBV2LIA
    c' <- transformPred sym c
    x' <- transformExprBV2LIA sym x
    y' <- transformExprBV2LIA sym y
    liftIO $ intIte sym c' x' y'

  | Just (BVShl w x y) <- asApp e
  , Just y_bv <- asBV y = do
    e' <- liftIO $ bvMul sym x =<< bvLit sym w (BV.mkBV w $ 2 ^ BV.asUnsigned y_bv)
    transformExprBV2LIA sym e'

  | Just (BVLshr w x y) <- asApp e
  , Just y_bv <- asBV y = do
    e' <- liftIO $ bvUdiv sym x =<< bvLit sym w (BV.mkBV w $ 2 ^ BV.asUnsigned y_bv)
    transformExprBV2LIA sym e'

  | Just (BVUdiv _w x y) <- asApp e
  , Just y_bv <- asBV y = do
    x' <- transformExprBV2LIA sym x
    y' <- liftIO $ intLit sym $ BV.asUnsigned y_bv
    liftIO $ intDiv sym x' y'

  | Just (BVUrem _w x y) <- asApp e
  , Just y_bv <- asBV y = do
    x' <- transformExprBV2LIA sym x
    y' <- liftIO $ intLit sym $ BV.asUnsigned y_bv
    liftIO $ intMod sym x' y'

  | otherwise = throwError $ "transformExprBV2LIA: unsupported " ++ show e

transformCmpLIA2BV ::
  ExprBuilder t st fs ->
  Expr t BaseBoolType ->
  Maybe (LIA2BVExprTransformer t (Expr t BaseBoolType))
transformCmpLIA2BV sym e
  | Just (BaseEq BaseIntegerRepr x y) <- asApp e = Just $ do
    let (x_pos, x_neg) = asPositiveNegativeWeightedSum x
    let (y_pos, y_neg) = asPositiveNegativeWeightedSum y
    x' <- liftIO $ semiRingSum sym $ WSum.add SR.SemiRingIntegerRepr x_pos y_neg
    y' <- liftIO $ semiRingSum sym $ WSum.add SR.SemiRingIntegerRepr y_pos x_neg
    x'' <- transformExprLIA2BV sym x'
    y'' <- transformExprLIA2BV sym y'
    liftIO $ bvEq sym x'' y''

  | Just (SemiRingLe SR.OrderedSemiRingIntegerRepr x y) <- asApp e = Just $ do
    z <- liftIO $ intSub sym x y
    let (z_pos, z_neg) = asPositiveNegativeWeightedSum z
    x' <- liftIO . bvSemiRingZext sym (knownNat :: NatRepr 72)
      =<< transformExprLIA2BV sym
      =<< liftIO (semiRingSum sym z_pos)
    y' <- liftIO . bvSemiRingZext sym (knownNat :: NatRepr 72)
      =<< transformExprLIA2BV sym
      =<< liftIO (semiRingSum sym z_neg)
    liftIO $ bvUle sym x' y'

  | otherwise = Nothing

asPositiveNegativeWeightedSum ::
  Expr t BaseIntegerType ->
  (WSum.WeightedSum (Expr t) SR.SemiRingInteger, WSum.WeightedSum (Expr t) SR.SemiRingInteger)
asPositiveNegativeWeightedSum e = do
  let semi_ring_sum = asWeightedSum SR.SemiRingIntegerRepr e
  let positive_semi_ring_sum = runIdentity $ WSum.traverseCoeffs
        (return . max 0)
        semi_ring_sum
  let negative_semi_ring_sum = runIdentity $ WSum.traverseCoeffs
        (return . negate . min 0)
        semi_ring_sum
  (positive_semi_ring_sum, negative_semi_ring_sum)

transformExprLIA2BV ::
  ExprBuilder t st fs ->
  Expr t BaseIntegerType ->
  LIA2BVExprTransformer t (Expr t (BaseBVType 64))
transformExprLIA2BV sym e
  | Just semi_ring_sum <- asSemiRingSum SR.SemiRingIntegerRepr e =
    liftIO . semiRingSum sym =<<
      WSum.transformSum
        (SR.SemiRingBVRepr SR.BVArithRepr knownNat)
        (return . BV.mkBV knownNat)
        (transformExprLIA2BV sym)
        semi_ring_sum

  | BoundVarExpr v <- e =
    BoundVarExpr <$> transformVarTp1ToTp2 sym v

  | Just (BaseIte _ _ c x y) <- asApp e = do
    let ?transformCmpTp1ToTp2 = transformCmpLIA2BV
        ?transformExprTp1ToTp2 = transformExprLIA2BV
    c' <- transformPred sym c
    x' <- transformExprLIA2BV sym x
    y' <- transformExprLIA2BV sym y
    liftIO $ bvIte sym c' x' y'

  | otherwise = throwError $ "transformExprLIA2BV: unsupported " ++ show e

bvSemiRingZext :: (1 <= w, 1 <= w', w + 1 <= w')
  => ExprBuilder t st fs
  -> NatRepr w'
  -> Expr t (BaseBVType w)
  -> IO (Expr t (BaseBVType w'))
bvSemiRingZext sym w' e
  | Just semi_ring_sum <- asSemiRingSum (SR.SemiRingBVRepr SR.BVArithRepr (bvWidth e)) e =
    liftIO . semiRingSum sym =<<
      WSum.transformSum
        (SR.SemiRingBVRepr SR.BVArithRepr w')
        (return . BV.zext w')
        (bvZext sym w')
        semi_ring_sum
  | otherwise = bvZext sym w' e

transformVarTp1ToTp2WithCont ::
  forall t st fs tp tp1 tp2 a .
  (KnownRepr BaseTypeRepr tp1, KnownRepr BaseTypeRepr tp2) =>
  ExprBuilder t st fs ->
  ExprBoundVar t tp ->
  (forall tp' . ExprBoundVar t tp' -> a) ->
  ExprTransformer t tp1 tp2 a
transformVarTp1ToTp2WithCont sym v k = applyTp1ToTp2FunWithCont (transformVarTp1ToTp2 sym) return k (bvarType v) v

transformVarTp1ToTp2 ::
  (KnownRepr BaseTypeRepr tp1, KnownRepr BaseTypeRepr tp2) =>
  ExprBuilder t st fs ->
  ExprBoundVar t tp1 ->
  ExprTransformer t tp1 tp2 (ExprBoundVar t tp2)
transformVarTp1ToTp2 sym v = do
  tbl <- asks transformerSubst
  liftIO $ mutateInsertIO tbl v $ sbMakeBoundVar sym (bvarName v) knownRepr (bvarKind v) Nothing

applyTp1ToTp2FunWithCont ::
  forall t tp tp1 tp2 e a .
  (KnownRepr BaseTypeRepr tp1, KnownRepr BaseTypeRepr tp2, Show (e tp)) =>
  (e tp1 -> ExprTransformer t tp1 tp2 (e tp2)) ->
  (e BaseBoolType -> ExprTransformer t tp1 tp2 (e BaseBoolType)) ->
  (forall tp' . e tp' -> a) ->
  BaseTypeRepr tp ->
  e tp ->
  ExprTransformer t tp1 tp2 a
applyTp1ToTp2FunWithCont f g k tp e
  | Just Refl <- testEquality (knownRepr :: BaseTypeRepr tp1) tp =
    k <$> f e
  | Just Refl <- testEquality BaseBoolRepr tp =
    k <$> g e
  | otherwise = throwError $ "applyTp1ToTp2FunWithCont: unsupported " ++ show e

mutateInsertIO ::
  (HC.HashTable h, Eq k, Hashable k) =>
  H.IOHashTable h k v ->
  k ->
  IO v ->
  IO v
mutateInsertIO tbl k f = H.mutateIO tbl k $ \case
  Just v -> return (Just v, v)
  Nothing -> do
    v <- f
    return (Just v, v)


-- | This attempts to lookup an entry in a symbolic array.
--
-- It patterns maps on the array constructor.
sbConcreteLookup :: forall t st fs d tp range
                 . ExprBuilder t st fs
                   -- ^ Simple builder for creating terms.
                 -> Expr t (BaseArrayType (d::>tp) range)
                    -- ^ Array to lookup value in.
                 -> Maybe (Ctx.Assignment IndexLit (d::>tp))
                    -- ^ A concrete index that corresponds to the index or nothing
                    -- if the index is symbolic.
                 -> Ctx.Assignment (Expr t) (d::>tp)
                    -- ^ The index to lookup.
                 -> IO (Expr t range)
sbConcreteLookup sym arr0 mcidx idx
    -- Try looking up a write to a concrete address.
  | Just (ArrayMap _ _ entry_map def) <- asApp arr0
  , Just cidx <- mcidx =
      case AUM.lookup cidx entry_map of
        Just v -> return v
        Nothing -> sbConcreteLookup sym def mcidx idx
    -- Evaluate function arrays on ground values.
  | Just (ArrayFromFn f) <- asNonceApp arr0 = do
      betaReduce sym f idx

    -- Lookups on constant arrays just return value
  | Just (ConstantArray _ _ v) <- asApp arr0 = do
      return v

    -- A lookup in an array update with symbolic update index is (i) the update
    -- value when the difference between the lookup index and the update index
    -- is zero, or (ii) a lookup in the update base array when the difference
    -- is a concrete non-zero number. Computing the difference instead of
    -- checking equality is more accurate because it enables the semi-rings and
    -- abstract domains simplifications (for example, `x` - `x + 1` simplifies
    -- to `1`)
  | Just (UpdateArray range idx_tps arr update_idx v) <- asApp arr0
  , Ctx.Empty Ctx.:> BaseBVRepr{} <- idx_tps
  , Ctx.Empty Ctx.:> idx0 <- idx
  , Ctx.Empty Ctx.:> update_idx0 <- update_idx = do
    diff <- bvSub sym idx0 update_idx0
    is_diff_zero <- bvEq sym diff =<< bvLit sym (bvWidth diff) (BV.zero (bvWidth diff))
    case asConstantPred is_diff_zero of
      Just True -> return v
      Just False -> sbConcreteLookup sym arr mcidx idx
      _ -> do
        (sliced_arr, sliced_idx) <- sliceArrayLookupUpdate sym arr0 idx
        sbMakeExpr sym (SelectArray range sliced_arr sliced_idx)

    -- A lookup in an array copy is a lookup in the src array when inside the copy range
  | Just (CopyArray w _a_repr _dest_arr dest_begin_idx src_arr src_begin_idx _len dest_end_idx _src_end_idx) <- asApp arr0
  , Just (Empty :> (BVIndexLit _ lookup_idx_bv)) <- mcidx
  , lookup_idx_unsigned <- BV.asUnsigned lookup_idx_bv
  , Just dest_begin_idx_unsigned <- BV.asUnsigned <$> asBV dest_begin_idx
  , Just dest_end_idx_unsigned <- BV.asUnsigned <$> asBV dest_end_idx
  , dest_begin_idx_unsigned <= lookup_idx_unsigned
  , lookup_idx_unsigned < dest_end_idx_unsigned = do
    new_lookup_idx <- bvAdd sym src_begin_idx =<<
      (bvLit sym w $ BV.mkBV w $ lookup_idx_unsigned - dest_begin_idx_unsigned)
    arrayLookup sym src_arr $ singleton new_lookup_idx
    -- A lookup in an array copy is a lookup in the dest array when outside the copy range
  | Just (CopyArray _w _a_repr dest_arr dest_begin_idx _src_arr _src_begin_idx _len _dest_end_idx _src_end_idx) <- asApp arr0
  , Just (Empty :> (BVIndexLit _ lookup_idx_bv)) <- mcidx
  , lookup_idx_unsigned <- BV.asUnsigned lookup_idx_bv
  , Just dest_begin_idx_unsigned <- BV.asUnsigned <$> asBV dest_begin_idx
  , lookup_idx_unsigned < dest_begin_idx_unsigned =
    sbConcreteLookup sym dest_arr mcidx idx
    -- A lookup in an array copy is a lookup in the dest array when outside the copy range
  | Just (CopyArray _w _a_repr dest_arr _dest_begin_idx _src_arr _src_begin_idx _len dest_end_idx _src_end_idx) <- asApp arr0
  , Just (Empty :> (BVIndexLit _ lookup_idx_bv)) <- mcidx
  , lookup_idx_unsigned <- BV.asUnsigned lookup_idx_bv
  , Just dest_end_idx_unsigned <- BV.asUnsigned <$> asBV dest_end_idx
  , dest_end_idx_unsigned <= lookup_idx_unsigned =
    sbConcreteLookup sym dest_arr mcidx idx

    -- A lookup in an array set returns the value when inside the set range
  | Just (SetArray _w _a_repr _arr begin_idx val _len end_idx) <- asApp arr0
  , Just (Empty :> (BVIndexLit _ lookup_idx_bv)) <- mcidx
  , lookup_idx_unsigned <- BV.asUnsigned lookup_idx_bv
  , Just begin_idx_unsigned <- BV.asUnsigned <$> asBV begin_idx
  , Just end_idx_unsigned <- BV.asUnsigned <$> asBV end_idx
  , begin_idx_unsigned <= lookup_idx_unsigned
  , lookup_idx_unsigned < end_idx_unsigned =
    return val
    -- A lookup in an array set is a lookup in the inner array when outside the set range
  | Just (SetArray _w _a_repr arr begin_idx _val _len _end_idx) <- asApp arr0
  , Just (Empty :> (BVIndexLit _ lookup_idx_bv)) <- mcidx
  , lookup_idx_unsigned <- BV.asUnsigned lookup_idx_bv
  , Just begin_idx_unsigned <- BV.asUnsigned <$> asBV begin_idx
  , lookup_idx_unsigned < begin_idx_unsigned =
    sbConcreteLookup sym arr mcidx idx
    -- A lookup in an array set is a lookup in the inner array when outside the set range
  | Just (SetArray _w _a_repr arr _begin_idx _val _len end_idx) <- asApp arr0
  , Just (Empty :> (BVIndexLit _ lookup_idx_bv)) <- mcidx
  , lookup_idx_unsigned <- BV.asUnsigned lookup_idx_bv
  , Just end_idx_unsigned <- BV.asUnsigned <$> asBV end_idx
  , end_idx_unsigned <= lookup_idx_unsigned =
    sbConcreteLookup sym arr mcidx idx

  | Just (MapOverArrays f _ args) <- asNonceApp arr0 = do
      let eval :: ArrayResultWrapper (Expr t) (d::>tp) utp
               -> IO (Expr t utp)
          eval a = sbConcreteLookup sym (unwrapArrayResult a) mcidx idx
      betaReduce sym f =<< traverseFC eval args
    -- Create select index.
  | otherwise = do
    case exprType arr0 of
      BaseArrayRepr _ range -> do
        (sliced_arr, sliced_idx) <- sliceArrayLookupUpdate sym arr0 idx
        sbMakeExpr sym (SelectArray range sliced_arr sliced_idx)

-- | Simplify an array lookup expression by slicing the array w.r.t. the index.
--
-- Remove array update, copy and set operations at indices that are different
-- from the lookup index.
sliceArrayLookupUpdate ::
  ExprBuilder t st fs ->
  Expr t (BaseArrayType (d::>tp) range) ->
  Ctx.Assignment (Expr t) (d::>tp) ->
  IO (Expr t (BaseArrayType (d::>tp) range), Ctx.Assignment (Expr t) (d::>tp))
sliceArrayLookupUpdate sym arr0 lookup_idx
  | Just (ArrayMap _ _ entry_map arr) <- asApp arr0 =
    case asConcreteIndices lookup_idx of
      Just lookup_concrete_idx ->
        case AUM.lookup lookup_concrete_idx entry_map of
          Just val -> do
            arr_base <- arrayUpdateBase sym arr
            sliced_arr <- arrayUpdate sym arr_base lookup_idx val
            return (sliced_arr, lookup_idx)
          Nothing -> sliceArrayLookupUpdate sym arr lookup_idx
      Nothing ->
        return (arr0, lookup_idx)

  | Just (CopyArray _w _a_repr dest_arr dest_begin_idx src_arr src_begin_idx len dest_end_idx _src_end_idx) <- asApp arr0 = do
    p0 <- bvUle sym dest_begin_idx (Ctx.last lookup_idx)
    p1 <- bvUlt sym (Ctx.last lookup_idx) dest_end_idx
    case (asConstantPred p0, asConstantPred p1) of
      (Just True, Just True) -> do
        new_lookup_idx <- bvAdd sym src_begin_idx =<<
          bvSub sym (Ctx.last lookup_idx) dest_begin_idx
        sliceArrayLookupUpdate sym src_arr $ singleton new_lookup_idx
      (Just False, _) ->
        sliceArrayLookupUpdate sym dest_arr lookup_idx
      (_, Just False) ->
        sliceArrayLookupUpdate sym dest_arr lookup_idx
      _ -> do
        (sliced_dest_arr, sliced_dest_idx) <- sliceArrayLookupUpdate sym dest_arr lookup_idx
        sliced_dest_begin_idx <- bvAdd sym dest_begin_idx =<<
          bvSub sym (Ctx.last sliced_dest_idx) (Ctx.last lookup_idx)
        sliced_arr <- arrayCopy sym sliced_dest_arr sliced_dest_begin_idx src_arr src_begin_idx len
        return (sliced_arr, sliced_dest_idx)

    -- A lookup in an array set returns the value when inside the set range
  | Just (SetArray _w _a_repr arr begin_idx val len end_idx) <- asApp arr0 = do
    p0 <- bvUle sym begin_idx (Ctx.last lookup_idx)
    p1 <- bvUlt sym (Ctx.last lookup_idx) end_idx
    case (asConstantPred p0, asConstantPred p1) of
      (Just True, Just True) -> do
        arr_base <- arrayUpdateBase sym arr
        sliced_arr <- arrayUpdate sym arr_base lookup_idx val
        return (sliced_arr, lookup_idx)
      (Just False, _) ->
        sliceArrayLookupUpdate sym arr lookup_idx
      (_, Just False) ->
        sliceArrayLookupUpdate sym arr lookup_idx
      _ -> do
        (sliced_arr, sliced_idx) <- sliceArrayLookupUpdate sym arr lookup_idx
        sliced_begin_idx <- bvAdd sym begin_idx =<<
          bvSub sym (Ctx.last sliced_idx) (Ctx.last lookup_idx)
        sliced_arr' <- arraySet sym sliced_arr sliced_begin_idx val len
        return (sliced_arr', sliced_idx)

    -- Lookups on mux arrays just distribute over mux.
  | Just (BaseIte _ _ p x y) <- asApp arr0 = do
      (x', i') <- sliceArrayLookupUpdate sym x lookup_idx
      (y', j') <- sliceArrayLookupUpdate sym y lookup_idx
      sliced_arr <- baseTypeIte sym p x' y'
      sliced_idx <- Ctx.zipWithM (baseTypeIte sym p) i' j'
      return (sliced_arr, sliced_idx)

  | otherwise = return (arr0, lookup_idx)

arrayUpdateBase ::
  ExprBuilder t st fs ->
  Expr t (BaseArrayType (d::>tp) range) ->
  IO (Expr t (BaseArrayType (d::>tp) range))
arrayUpdateBase sym arr0 = case asApp arr0 of
  Just (UpdateArray _ _ arr _ _) -> arrayUpdateBase sym arr
  Just (ArrayMap _ _ _ arr) -> arrayUpdateBase sym arr
  Just (CopyArray _ _ arr _ _ _ _ _ _) -> arrayUpdateBase sym arr
  Just (SetArray _ _ arr _ _ _ _) -> arrayUpdateBase sym arr
  Just (BaseIte _ _ p x y) -> do
    x' <- arrayUpdateBase sym x
    y' <- arrayUpdateBase sym y
    baseTypeIte sym p x' y'
  _ -> return arr0

----------------------------------------------------------------------
-- Expression builder instances

-- | Evaluate a weighted sum of integer values.
intSum :: ExprBuilder t st fs -> WeightedSum (Expr t) SR.SemiRingInteger -> IO (IntegerExpr t)
intSum sym s = semiRingSum sym s

-- | Evaluate a weighted sum of real values.
realSum :: ExprBuilder t st fs -> WeightedSum (Expr t) SR.SemiRingReal -> IO (RealExpr t)
realSum sym s = semiRingSum sym s

bvSum :: ExprBuilder t st fs -> WeightedSum (Expr t) (SR.SemiRingBV flv w) -> IO (BVExpr t w)
bvSum sym s = semiRingSum sym s

conjPred :: ExprBuilder t st fs -> BoolMap (Expr t) -> IO (BoolExpr t)
conjPred sym bm =
  case BM.viewBoolMap bm of
    BoolMapUnit     -> return $ truePred sym
    BoolMapDualUnit -> return $ falsePred sym
    BoolMapTerms ((x,p):|[]) ->
      case p of
        Positive -> return x
        Negative -> notPred sym x
    _ -> sbMakeExpr sym $ ConjPred bm

bvUnary :: (1 <= w) => ExprBuilder t st fs -> UnaryBV (BoolExpr t) w -> IO (BVExpr t w)
bvUnary sym u
  -- BGS: We probably don't need to re-truncate the result, but
  -- until we refactor UnaryBV to use BV w instead of integer,
  -- that'll have to wait.
  | Just v <-  UnaryBV.asConstant u = bvLit sym w (BV.mkBV w v)
  | otherwise = sbMakeExpr sym (BVUnaryTerm u)
  where w = UnaryBV.width u

asUnaryBV :: (?unaryThreshold :: Int)
          => ExprBuilder t st fs
          -> BVExpr t n
          -> Maybe (UnaryBV (BoolExpr t) n)
asUnaryBV sym e
  | Just (BVUnaryTerm u) <- asApp e = Just u
  | ?unaryThreshold == 0 = Nothing
  | SemiRingLiteral (SR.SemiRingBVRepr _ w) v _ <- e = Just $ UnaryBV.constant sym w (BV.asUnsigned v)
  | otherwise = Nothing

-- | This create a unary bitvector representing if the size is not too large.
sbTryUnaryTerm :: (1 <= w, ?unaryThreshold :: Int)
               => ExprBuilder t st fs
               -> Maybe (IO (UnaryBV (BoolExpr t) w))
               -> IO (BVExpr t w)
               -> IO (BVExpr t w)
sbTryUnaryTerm _sym Nothing fallback = fallback
sbTryUnaryTerm sym (Just mku) fallback =
  do u <- mku
     if UnaryBV.size u < ?unaryThreshold then
       bvUnary sym u
     else
       fallback

semiRingProd ::
  ExprBuilder t st fs ->
  SemiRingProduct (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingProd sym pd
  | WSum.nullProd pd = semiRingLit sym (WSum.prodRepr pd) (SR.one (WSum.prodRepr pd))
  | Just v <- WSum.asProdVar pd = return v
  | otherwise = sbMakeExpr sym $ SemiRingProd pd

semiRingSum ::
  ExprBuilder t st fs ->
  WeightedSum (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingSum sym s
    | Just c <- WSum.asConstant s = semiRingLit sym (WSum.sumRepr s) c
    | Just r <- WSum.asVar s      = return r
    | otherwise                   = sum' sym s

sum' ::
  ExprBuilder t st fs ->
  WeightedSum (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
sum' sym s = sbMakeExpr sym $ SemiRingSum s
{-# INLINE sum' #-}

scalarMul ::
   ExprBuilder t st fs ->
   SR.SemiRingRepr sr ->
   SR.Coefficient sr ->
   Expr t (SR.SemiRingBase sr) ->
   IO (Expr t (SR.SemiRingBase sr))
scalarMul sym sr c x
  | SR.eq sr (SR.zero sr) c = semiRingLit sym sr (SR.zero sr)
  | SR.eq sr (SR.one sr)  c = return x
  | Just r <- asSemiRingLit sr x =
    semiRingLit sym sr (SR.mul sr c r)
  | Just s <- asSemiRingSum sr x =
    sum' sym (WSum.scale sr c s)
  | otherwise =
    sum' sym (WSum.scaledVar sr c x)

semiRingIte ::
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  Expr t BaseBoolType ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingIte sym sr c x y
    -- evaluate as constants
  | Just True  <- asConstantPred c = return x
  | Just False <- asConstantPred c = return y

    -- reduce negations
  | Just (NotPred c') <- asApp c
  = semiRingIte sym sr c' y x

    -- remove the ite if the then and else cases are the same
  | x == y = return x

    -- Try to extract common sum information.
  | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
  , not (WSum.isZero sr z) = do
    xr <- semiRingSum sym x'
    yr <- semiRingSum sym y'
    let sz = 1 + iteSize xr + iteSize yr
    r <- sbMakeExpr sym (BaseIte (SR.semiRingBase sr) sz c xr yr)
    semiRingSum sym $! WSum.addVar sr z r

    -- final fallback, create the ite term
  | otherwise =
      let sz = 1 + iteSize x + iteSize y in
      sbMakeExpr sym (BaseIte (SR.semiRingBase sr) sz c x y)


mkIte ::
  ExprBuilder t st fs ->
  Expr t BaseBoolType ->
  Expr t bt ->
  Expr t bt ->
  IO (Expr t bt)
mkIte sym c x y
    -- evaluate as constants
  | Just True  <- asConstantPred c = return x
  | Just False <- asConstantPred c = return y

    -- reduce negations
  | Just (NotPred c') <- asApp c
  = mkIte sym c' y x

    -- remove the ite if the then and else cases are the same
  | x == y = return x

  | otherwise =
      let sz = 1 + iteSize x + iteSize y in
      sbMakeExpr sym (BaseIte (exprType x) sz c x y)

semiRingLe ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  (Expr t (SR.SemiRingBase sr) -> Expr t (SR.SemiRingBase sr) -> IO (Expr t BaseBoolType))
      {- ^ recursive call for simplifications -} ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t BaseBoolType)
semiRingLe sym osr rec x y
      -- Check for syntactic equality.
    | x == y = return (truePred sym)

      -- Strength reductions on a non-linear constraint to piecewise linear.
    | Just c <- asSemiRingLit sr x
    , SR.eq sr c (SR.zero sr)
    , Just (SemiRingProd pd) <- asApp y
    , Just Refl <- testEquality sr (WSum.prodRepr pd)
    = prodNonneg sym osr pd

      -- Another strength reduction
    | Just c <- asSemiRingLit sr y
    , SR.eq sr c (SR.zero sr)
    , Just (SemiRingProd pd) <- asApp x
    , Just Refl <- testEquality sr (WSum.prodRepr pd)
    = prodNonpos sym osr pd

      -- Push some comparisons under if/then/else
    | SemiRingLiteral _ _ _ <- x
    , Just (BaseIte _ _ c a b) <- asApp y
    = join (itePred sym c <$> rec x a <*> rec x b)

      -- Push some comparisons under if/then/else
    | Just (BaseIte tp _ c a b) <- asApp x
    , SemiRingLiteral _ _ _ <- y
    , Just Refl <- testEquality tp (SR.semiRingBase sr)
    = join (itePred sym c <$> rec a y <*> rec b y)

      -- Try to extract common sum information.
    | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
    , not (WSum.isZero sr z) = do
      xr <- semiRingSum sym x'
      yr <- semiRingSum sym y'
      rec xr yr

      -- Default case
    | otherwise = sbMakeExpr sym $ SemiRingLe osr x y

 where sr = SR.orderedSemiRing osr


semiRingEq ::
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  (Expr t (SR.SemiRingBase sr) -> Expr t (SR.SemiRingBase sr) -> IO (Expr t BaseBoolType))
    {- ^ recursive call for simplifications -} ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t BaseBoolType)
semiRingEq sym sr rec x y
  -- Check for syntactic equality.
  | x == y = return (truePred sym)

    -- Push some equalities under if/then/else
  | SemiRingLiteral _ _ _ <- x
  , Just (BaseIte _ _ c a b) <- asApp y
  = join (itePred sym c <$> rec x a <*> rec x b)

    -- Push some equalities under if/then/else
  | Just (BaseIte _ _ c a b) <- asApp x
  , SemiRingLiteral _ _ _ <- y
  = join (itePred sym c <$> rec a y <*> rec b y)

  | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
  , not (WSum.isZero sr z) =
    case (WSum.asConstant x', WSum.asConstant y') of
      (Just a, Just b) -> return $! backendPred sym (SR.eq sr a b)
      _ -> do xr <- semiRingSum sym x'
              yr <- semiRingSum sym y'
              sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min xr yr) (max xr yr)

  | otherwise =
    sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min x y) (max x y)

semiRingAdd ::
  forall t st fs sr.
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingAdd sym sr x y =
    case (viewSemiRing sr x, viewSemiRing sr y) of
      (SR_Constant c, _) | SR.eq sr c (SR.zero sr) -> return y
      (_, SR_Constant c) | SR.eq sr c (SR.zero sr) -> return x

      (SR_Constant xc, SR_Constant yc) ->
        semiRingLit sym sr (SR.add sr xc yc)

      (SR_Constant xc, SR_Sum ys) ->
        sum' sym (WSum.addConstant sr ys xc)
      (SR_Sum xs, SR_Constant yc) ->
        sum' sym (WSum.addConstant sr xs yc)

      (SR_Constant xc, _)
        | Just (BaseIte _ _ cond a b) <- asApp y
        , isConstantSemiRingExpr a || isConstantSemiRingExpr b -> do
            xa <- semiRingAdd sym sr x a
            xb <- semiRingAdd sym sr x b
            semiRingIte sym sr cond xa xb
        | otherwise ->
            sum' sym (WSum.addConstant sr (WSum.var sr y) xc)

      (_, SR_Constant yc)
        | Just (BaseIte _ _ cond a b) <- asApp x
        , isConstantSemiRingExpr a || isConstantSemiRingExpr b -> do
            ay <- semiRingAdd sym sr a y
            by <- semiRingAdd sym sr b y
            semiRingIte sym sr cond ay by
        | otherwise ->
            sum' sym (WSum.addConstant sr (WSum.var sr x) yc)

      (SR_Sum xs, SR_Sum ys) -> semiRingSum sym (WSum.add sr xs ys)
      (SR_Sum xs, _)         -> semiRingSum sym (WSum.addVar sr xs y)
      (_ , SR_Sum ys)        -> semiRingSum sym (WSum.addVar sr ys x)
      _                      -> semiRingSum sym (WSum.addVars sr x y)
  where isConstantSemiRingExpr :: Expr t (SR.SemiRingBase sr) -> Bool
        isConstantSemiRingExpr (viewSemiRing sr -> SR_Constant _) = True
        isConstantSemiRingExpr _ = False

semiRingMul ::
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingMul sym sr x y =
  case (viewSemiRing sr x, viewSemiRing sr y) of
    (SR_Constant c, _) -> scalarMul sym sr c y
    (_, SR_Constant c) -> scalarMul sym sr c x

    (SR_Sum (WSum.asAffineVar -> Just (c,x',o)), _) ->
      do cxy <- scalarMul sym sr c =<< semiRingMul sym sr x' y
         oy  <- scalarMul sym sr o y
         semiRingAdd sym sr cxy oy

    (_, SR_Sum (WSum.asAffineVar -> Just (c,y',o))) ->
      do cxy <- scalarMul sym sr c =<< semiRingMul sym sr x y'
         ox  <- scalarMul sym sr o x
         semiRingAdd sym sr cxy ox

    (SR_Prod px, SR_Prod py) -> semiRingProd sym (WSum.prodMul px py)
    (SR_Prod px, _)          -> semiRingProd sym (WSum.prodMul px (WSum.prodVar sr y))
    (_, SR_Prod py)          -> semiRingProd sym (WSum.prodMul (WSum.prodVar sr x) py)
    _                        -> semiRingProd sym (WSum.prodMul (WSum.prodVar sr x) (WSum.prodVar sr y))


prodNonneg ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType)
prodNonneg sym osr pd =
  do let sr = SR.orderedSemiRing osr
     zero <- semiRingLit sym sr (SR.zero sr)
     fst <$> computeNonnegNonpos sym osr zero pd

prodNonpos ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType)
prodNonpos sym osr pd =
  do let sr = SR.orderedSemiRing osr
     zero <- semiRingLit sym sr (SR.zero sr)
     snd <$> computeNonnegNonpos sym osr zero pd

computeNonnegNonpos ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) {- zero element -} ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType, Expr t BaseBoolType)
computeNonnegNonpos sym osr zero pd =
   fromMaybe (truePred sym, falsePred sym) <$> WSum.prodEvalM merge single pd
 where

 single x = (,) <$> reduceApp sym bvUnary (SemiRingLe osr zero x) -- nonnegative
                <*> reduceApp sym bvUnary (SemiRingLe osr x zero) -- nonpositive

 merge (nn1, np1) (nn2, np2) =
   do nn <- join (orPred sym <$> andPred sym nn1 nn2 <*> andPred sym np1 np2)
      np <- join (orPred sym <$> andPred sym nn1 np2 <*> andPred sym np1 nn2)
      return (nn, np)



arrayResultIdxType :: BaseTypeRepr (BaseArrayType (idx ::> itp) d)
                   -> Ctx.Assignment BaseTypeRepr (idx ::> itp)
arrayResultIdxType (BaseArrayRepr idx _) = idx

-- | This decomposes A ExprBuilder array expression into a set of indices that
-- have been updated, and an underlying index.
data ArrayMapView i f tp
   = ArrayMapView { _arrayMapViewIndices :: !(AUM.ArrayUpdateMap f i tp)
                  , _arrayMapViewExpr    :: !(f (BaseArrayType i tp))
                  }

-- | Construct an 'ArrayMapView' for an element.
viewArrayMap :: Expr t (BaseArrayType i tp)
             -> ArrayMapView i (Expr t) tp
viewArrayMap  x
  | Just (ArrayMap _ _ m c) <- asApp x = ArrayMapView m c
  | otherwise = ArrayMapView AUM.empty x

-- | Construct an 'ArrayMapView' for an element.
underlyingArrayMapExpr :: ArrayResultWrapper (Expr t) i tp
                      -> ArrayResultWrapper (Expr t) i tp
underlyingArrayMapExpr x
  | Just (ArrayMap _ _ _ c) <- asApp (unwrapArrayResult x) = ArrayResultWrapper c
  | otherwise = x

-- | Return set of addresss in assignment that are written to by at least one expr
concreteArrayEntries :: forall t i ctx
                     .  Ctx.Assignment (ArrayResultWrapper (Expr t) i) ctx
                     -> Set (Ctx.Assignment IndexLit i)
concreteArrayEntries = foldlFC' f Set.empty
  where f :: Set (Ctx.Assignment IndexLit i)
          -> ArrayResultWrapper (Expr t) i tp
          -> Set (Ctx.Assignment IndexLit i)
        f s e
          | Just (ArrayMap _ _ m _) <- asApp (unwrapArrayResult  e) =
            Set.union s (AUM.keysSet m)
          | otherwise = s



data IntLit tp = (tp ~ BaseIntegerType) => IntLit Integer

asIntBounds :: Ctx.Assignment (Expr t) idx -> Maybe (Ctx.Assignment IntLit idx)
asIntBounds = traverseFC f
  where f :: Expr t tp -> Maybe (IntLit tp)
        f (SemiRingLiteral SR.SemiRingIntegerRepr n _) = Just (IntLit n)
        f _ = Nothing

foldBoundLeM :: (r -> Integer -> IO r) -> r -> Integer -> IO r
foldBoundLeM f r n
  | n <= 0 = pure r
  | otherwise =
      do r' <- foldBoundLeM f r (n-1)
         f r' n

foldIndicesInRangeBounds :: forall sym idx r
                         .  IsExprBuilder sym
                         => sym
                         -> (r -> Ctx.Assignment (SymExpr sym) idx -> IO r)
                         -> r
                         -> Ctx.Assignment IntLit idx
                         -> IO r
foldIndicesInRangeBounds sym f0 a0 bnds0 = do
  case bnds0 of
    Ctx.Empty -> f0 a0 Ctx.empty
    bnds Ctx.:> IntLit b -> foldIndicesInRangeBounds sym (g f0) a0 bnds
      where g :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseIntegerType) -> IO r)
              -> r
              -> Ctx.Assignment (SymExpr sym) idx0
              -> IO r
            g f a i = foldBoundLeM (h f i) a b

            h :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseIntegerType) -> IO r)
              -> Ctx.Assignment (SymExpr sym) idx0
              -> r
              -> Integer
              -> IO r
            h f i a j = do
              je <- intLit sym j
              f a (i Ctx.:> je)

-- | Examine the list of terms, and determine if any one of them
--   appears in the given @BoolMap@ with the same polarity.
checkAbsorption ::
  BoolMap (Expr t) ->
  [(BoolExpr t, Polarity)] ->
  Bool
checkAbsorption _bm [] = False
checkAbsorption bm ((x,p):_)
  | Just p' <- BM.contains bm x, p == p' = True
checkAbsorption bm (_:xs) = checkAbsorption bm xs

-- | If @tryAndAbsorption x y@ returns @True@, that means that @y@
-- implies @x@, so that the conjunction @x AND y = y@. A @False@
-- result gives no information.
tryAndAbsorption ::
  BoolExpr t ->
  BoolExpr t ->
  Bool
tryAndAbsorption (asApp -> Just (NotPred (asApp -> Just (ConjPred as)))) (asConjunction -> bs)
  = checkAbsorption (BM.reversePolarities as) bs
tryAndAbsorption _ _ = False


-- | If @tryOrAbsorption x y@ returns @True@, that means that @x@
-- implies @y@, so that the disjunction @x OR y = y@. A @False@
-- result gives no information.
tryOrAbsorption ::
  BoolExpr t ->
  BoolExpr t ->
  Bool
tryOrAbsorption (asApp -> Just (ConjPred as)) (asDisjunction -> bs)
  = checkAbsorption as bs
tryOrAbsorption _ _ = False



instance IsExprBuilder (ExprBuilder t st fs) where
  getConfiguration = sbConfiguration

  setSolverLogListener sb = atomicWriteIORef (sbSolverLogger sb)
  getSolverLogListener sb = readIORef (sbSolverLogger sb)

  logSolverEvent sb ev =
    readIORef (sbSolverLogger sb) >>= \case
      Nothing -> return ()
      Just f  -> f ev

  getStatistics sb = do
    allocs <- countNoncesGenerated (sbExprCounter sb)
    nonLinearOps <- readIORef (sbNonLinearOps sb)
    return $ Statistics { statAllocs = allocs
                        , statNonLinearOps = nonLinearOps }

  annotateTerm sym e =
    case e of
      BoundVarExpr (bvarId -> n) -> return (n, e)
      NonceAppExpr (nonceExprApp -> Annotation _ n _) -> return (n, e)
      _ -> do
        let tpr = exprType e
        n <- sbFreshIndex sym
        e' <- sbNonceExpr sym (Annotation tpr n e)
        return (n, e')

  getAnnotation _sym e =
    case e of
      BoundVarExpr (bvarId -> n) -> Just n
      NonceAppExpr (nonceExprApp -> Annotation _ n _) -> Just n
      _ -> Nothing

  getUnannotatedTerm _sym e =
    case e of
      NonceAppExpr (nonceExprApp -> Annotation _ _ x) -> Just x
      _ -> Nothing

  ----------------------------------------------------------------------
  -- Program location operations

  getCurrentProgramLoc = curProgramLoc
  setCurrentProgramLoc sym l = atomicWriteIORef (sbProgramLoc sym) l

  ----------------------------------------------------------------------
  -- Bool operations.

  truePred  = sbTrue
  falsePred = sbFalse

  notPred sym x
    | Just b <- asConstantPred x
    = return (backendPred sym $! not b)

    | Just (NotPred x') <- asApp x
    = return x'

    | otherwise
    = sbMakeExpr sym (NotPred x)

  eqPred sym x y
    | x == y
    = return (truePred sym)

    | Just (NotPred x') <- asApp x
    = xorPred sym x' y

    | Just (NotPred y') <- asApp y
    = xorPred sym x y'

    | otherwise
    = case (asConstantPred x, asConstantPred y) of
        (Just False, _)    -> notPred sym y
        (Just True, _)     -> return y
        (_, Just False)    -> notPred sym x
        (_, Just True)     -> return x
        _ -> sbMakeExpr sym $ BaseEq BaseBoolRepr (min x y) (max x y)

  xorPred sym x y = notPred sym =<< eqPred sym x y

  andPred sym x y =
    case (asConstantPred x, asConstantPred y) of
      (Just True, _)  -> return y
      (Just False, _) -> return x
      (_, Just True)  -> return x
      (_, Just False) -> return y
      _ | x == y -> return x -- and is idempotent
        | otherwise -> go x y

   where
   go a b
     | Just (ConjPred as) <- asApp a
     , Just (ConjPred bs) <- asApp b
     = conjPred sym $ BM.combine as bs

     | tryAndAbsorption a b
     = return b

     | tryAndAbsorption b a
     = return a

     | Just (ConjPred as) <- asApp a
     = conjPred sym $ uncurry BM.addVar (asPosAtom b) as

     | Just (ConjPred bs) <- asApp b
     = conjPred sym $ uncurry BM.addVar (asPosAtom a) bs

     | otherwise
     = conjPred sym $ BM.fromVars [asPosAtom a, asPosAtom b]

  orPred sym x y =
    case (asConstantPred x, asConstantPred y) of
      (Just True, _)  -> return x
      (Just False, _) -> return y
      (_, Just True)  -> return y
      (_, Just False) -> return x
      _ | x == y -> return x -- or is idempotent
        | otherwise -> go x y

   where
   go a b
     | Just (NotPred (asApp -> Just (ConjPred as))) <- asApp a
     , Just (NotPred (asApp -> Just (ConjPred bs))) <- asApp b
     = notPred sym =<< conjPred sym (BM.combine as bs)

     | tryOrAbsorption a b
     = return b

     | tryOrAbsorption b a
     = return a

     | Just (NotPred (asApp -> Just (ConjPred as))) <- asApp a
     = notPred sym =<< conjPred sym (uncurry BM.addVar (asNegAtom b) as)

     | Just (NotPred (asApp -> Just (ConjPred bs))) <- asApp b
     = notPred sym =<< conjPred sym (uncurry BM.addVar (asNegAtom a) bs)

     | otherwise
     = notPred sym =<< conjPred sym (BM.fromVars [asNegAtom a, asNegAtom b])

  itePred sb c x y
      -- ite c c y = c || y
    | c == x = orPred sb c y

      -- ite c x c = c && x
    | c == y = andPred sb c x

      -- ite c x x = x
    | x == y = return x

      -- ite 1 x y = x
    | Just True  <- asConstantPred c = return x

      -- ite 0 x y = y
    | Just False <- asConstantPred c = return y

      -- ite !c x y = ite c y x
    | Just (NotPred c') <- asApp c = itePred sb c' y x

      -- ite c 1 y = c || y
    | Just True  <- asConstantPred x = orPred sb c y

      -- ite c 0 y = !c && y
    | Just False <- asConstantPred x = andPred sb y =<< notPred sb c

      -- ite c x 1 = !c || x
    | Just True  <- asConstantPred y = orPred sb x =<< notPred sb c

      -- ite c x 0 = c && x
    | Just False <- asConstantPred y = andPred sb c x

      -- Default case
    | otherwise =
        let sz = 1 + iteSize x + iteSize y in
        sbMakeExpr sb $ BaseIte BaseBoolRepr sz c x y

  ----------------------------------------------------------------------
  -- Integer operations.

  intLit sym n = semiRingLit sym SR.SemiRingIntegerRepr n

  intNeg sym x = scalarMul sym SR.SemiRingIntegerRepr (-1) x

  intAdd sym x y = semiRingAdd sym SR.SemiRingIntegerRepr x y

  intMul sym x y = semiRingMul sym SR.SemiRingIntegerRepr x y

  intIte sym c x y = semiRingIte sym SR.SemiRingIntegerRepr c x y

  intEq sym x y
      -- Use range check
    | Just b <- rangeCheckEq (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to bitvector equality, when possible
    | Just (SBVToInteger xbv) <- asApp x
    , Just (SBVToInteger ybv) <- asApp y
    = let wx = bvWidth xbv
          wy = bvWidth ybv
          -- Sign extend to largest bitvector and compare.
       in case testNatCases wx wy of
            NatCaseLT LeqProof -> do
              x' <- bvSext sym wy xbv
              bvEq sym x' ybv
            NatCaseEQ ->
              bvEq sym xbv ybv
            NatCaseGT LeqProof -> do
              y' <- bvSext sym wx ybv
              bvEq sym xbv y'

      -- Reduce to bitvector equality, when possible
    | Just (BVToInteger xbv) <- asApp x
    , Just (BVToInteger ybv) <- asApp y
    = let wx = bvWidth xbv
          wy = bvWidth ybv
          -- Zero extend to largest bitvector and compare.
       in case testNatCases wx wy of
            NatCaseLT LeqProof -> do
              x' <- bvZext sym wy xbv
              bvEq sym x' ybv
            NatCaseEQ ->
              bvEq sym xbv ybv
            NatCaseGT LeqProof -> do
              y' <- bvZext sym wx ybv
              bvEq sym xbv y'

    | Just (SBVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if yi < minSigned w || yi > maxSigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w (BV.mkBV w yi)

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minSigned w || xi > maxSigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w (BV.mkBV w xi)

    | Just (BVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if yi < minUnsigned w || yi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w (BV.mkBV w yi)

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (BVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minUnsigned w || xi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w (BV.mkBV w xi)

    | otherwise = semiRingEq sym SR.SemiRingIntegerRepr (intEq sym) x y

  intLe sym x y
      -- Use abstract domains
    | Just b <- rangeCheckLe (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Check with two bitvectors.
    | Just (SBVToInteger xbv) <- asApp x
    , Just (SBVToInteger ybv) <- asApp y
    = do let wx = bvWidth xbv
         let wy = bvWidth ybv
         -- Sign extend to largest bitvector and compare.
         case testNatCases wx wy of
           NatCaseLT LeqProof -> do
             x' <- bvSext sym wy xbv
             bvSle sym x' ybv
           NatCaseEQ -> bvSle sym xbv ybv
           NatCaseGT LeqProof -> do
             y' <- bvSext sym wx ybv
             bvSle sym xbv y'

      -- Check with two bitvectors.
    | Just (BVToInteger xbv) <- asApp x
    , Just (BVToInteger ybv) <- asApp y
    = do let wx = bvWidth xbv
         let wy = bvWidth ybv
         -- Zero extend to largest bitvector and compare.
         case testNatCases wx wy of
           NatCaseLT LeqProof -> do
             x' <- bvZext sym wy xbv
             bvUle sym x' ybv
           NatCaseEQ -> bvUle sym xbv ybv
           NatCaseGT LeqProof -> do
             y' <- bvZext sym wx ybv
             bvUle sym xbv y'

    | Just (SBVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if | yi < minSigned w -> return (falsePred sym)
         | yi > maxSigned w -> return (truePred sym)
         | otherwise -> join (bvSle sym <$> pure xbv <*> bvLit sym w (BV.mkBV w yi))

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if | xi < minSigned w -> return (truePred sym)
         | xi > maxSigned w -> return (falsePred sym)
         | otherwise -> join (bvSle sym <$> bvLit sym w (BV.mkBV w xi) <*> pure ybv)

    | Just (BVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if | yi < minUnsigned w -> return (falsePred sym)
         | yi > maxUnsigned w -> return (truePred sym)
         | otherwise -> join (bvUle sym <$> pure xbv <*> bvLit sym w (BV.mkBV w yi))

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (BVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if | xi < minUnsigned w -> return (truePred sym)
         | xi > maxUnsigned w -> return (falsePred sym)
         | otherwise -> join (bvUle sym <$> bvLit sym w (BV.mkBV w xi) <*> pure ybv)

{-  FIXME? how important are these reductions?

      -- Compare to BV lower bound.
    | Just (SBVToInteger xbv) <- x = do
      let w = bvWidth xbv
      l <- curProgramLoc sym
      b_max <- realGe sym y (SemiRingLiteral SemiRingReal (toRational (maxSigned w)) l)
      b_min <- realGe sym y (SemiRingLiteral SemiRingReal (toRational (minSigned w)) l)
      orPred sym b_max =<< andPred sym b_min =<< (bvSle sym xbv =<< realToSBV sym w y)

      -- Compare to SBV upper bound.
    | SBVToReal ybv <- y = do
      let w = bvWidth ybv
      l <- curProgramLoc sym
      b_min <- realLe sym x (SemiRingLiteral SemiRingReal (toRational (minSigned w)) l)
      b_max <- realLe sym x (SemiRingLiteral SemiRingReal (toRational (maxSigned w)) l)
      orPred sym b_min
        =<< andPred sym b_max
        =<< (\xbv -> bvSle sym xbv ybv) =<< realToSBV sym w x
-}

    | otherwise
    = semiRingLe sym SR.OrderedSemiRingIntegerRepr (intLe sym) x y

  intAbs sym x
    | Just i <- asInteger x = intLit sym (abs i)
    | Just True <- rangeCheckLe (SingleRange 0) (exprAbsValue x) = return x
    | Just True <- rangeCheckLe (exprAbsValue x) (SingleRange 0) = intNeg sym x
    | otherwise = sbMakeExpr sym (IntAbs x)

  intDiv sym x y
      -- Div by 1.
    | Just 1 <- asInteger y = return x
      -- As integers.
    | Just xi <- asInteger x, Just yi <- asInteger y, yi /= 0 =
      if yi >= 0 then
        intLit sym (xi `div` yi)
      else
        intLit sym (negate (xi `div` negate yi))
      -- Return int div
    | otherwise =
        sbMakeExpr sym (IntDiv x y)

  intMod sym x y
      -- Mod by 1.
    | Just 1 <- asInteger y = intLit sym 0
      -- As integers.
    | Just xi <- asInteger x, Just yi <- asInteger y, yi /= 0 =
        intLit sym (xi `mod` abs yi)
    | Just (SemiRingSum xsum) <- asApp x
    , SR.SemiRingIntegerRepr <- WSum.sumRepr xsum
    , Just yi <- asInteger y
    , yi /= 0 =
        case WSum.reduceIntSumMod xsum (abs yi) of
          xsum' | Just xi <- WSum.asConstant xsum' ->
                    intLit sym xi
                | otherwise ->
                    do x' <- intSum sym xsum'
                       sbMakeExpr sym (IntMod x' y)
      -- Return int mod.
    | otherwise =
        sbMakeExpr sym (IntMod x y)

  intDivisible sym x k
    | k == 0 = intEq sym x =<< intLit sym 0
    | k == 1 = return (truePred sym)
    | Just xi <- asInteger x = return $ backendPred sym (xi `mod` (toInteger k) == 0)
    | Just (SemiRingSum xsum) <- asApp x
    , SR.SemiRingIntegerRepr <- WSum.sumRepr xsum =
        case WSum.reduceIntSumMod xsum (toInteger k) of
          xsum' | Just xi <- WSum.asConstant xsum' ->
                    return $ backendPred sym (xi == 0)
                | otherwise ->
                    do x' <- intSum sym xsum'
                       sbMakeExpr sym (IntDivisible x' k)
    | otherwise =
        sbMakeExpr sym (IntDivisible x k)

  ---------------------------------------------------------------------
  -- Bitvector operations

  bvLit sym w bv =
    semiRingLit sym (SR.SemiRingBVRepr SR.BVArithRepr w) bv

  bvConcat sym x y =
    case (asBV x, asBV y) of
      -- both values are constants, just compute the concatenation
      (Just xv, Just yv) -> do
          let w' = addNat (bvWidth x) (bvWidth y)
          LeqProof <- return (leqAddPos (bvWidth x) (bvWidth y))
          bvLit sym w' (BV.concat (bvWidth x) (bvWidth y) xv yv)
      -- reassociate to combine constants where possible
      (Just _xv, _)
        | Just (BVConcat _w a b) <- asApp y
        , Just _av <- asBV a
        , Just Refl <- testEquality (addNat (bvWidth x) (addNat (bvWidth a) (bvWidth b)))
                        (addNat (addNat (bvWidth x) (bvWidth a)) (bvWidth b))
        , Just LeqProof <- isPosNat (addNat (bvWidth x) (bvWidth a)) -> do
            xa <- bvConcat sym x a
            bvConcat sym xa b
      -- concat two adjacent sub-selects just makes a single select
      _ | Just (BVSelect idx1 n1 a) <- asApp x
        , Just (BVSelect idx2 n2 b) <- asApp y
        , Just Refl <- sameTerm a b
        , Just Refl <- testEquality idx1 (addNat idx2 n2)
        , Just LeqProof <- isPosNat (addNat n1 n2)
        , Just LeqProof <- testLeq (addNat idx2 (addNat n1 n2)) (bvWidth a) ->
            bvSelect sym idx2 (addNat n1 n2) a
      -- always reassociate to the right
      _ | Just (BVConcat _w a b) <- asApp x
        , Just _bv <- asBV b
        , Just Refl <- testEquality (addNat (bvWidth a) (addNat (bvWidth b) (bvWidth y)))
                        (addNat (addNat (bvWidth a) (bvWidth b)) (bvWidth y))
        , Just LeqProof <- isPosNat (addNat (bvWidth b) (bvWidth y)) -> do
            by <- bvConcat sym b y
            bvConcat sym a by
      -- no special case applies, emit a basic concat expression
      _ -> do
        let wx = bvWidth x
        let wy = bvWidth y
        Just LeqProof <- return (isPosNat (addNat wx wy))
        sbMakeExpr sym $ BVConcat (addNat wx wy) x y

  -- bvSelect has a bunch of special cases that examine the form of the
  -- bitvector being selected from.  This can significantly reduce the size
  -- of expressions that result from the very verbose packing and unpacking
  -- operations that arise from byte-oriented memory models.
  bvSelect sb idx n x
    | Just xv <- asBV x = do
      bvLit sb n (BV.select idx n xv)

      -- nested selects can be collapsed
    | Just (BVSelect idx' _n' b) <- asApp x
    , let idx2 = addNat idx idx'
    , Just LeqProof <- testLeq (addNat idx2 n) (bvWidth b) =
      bvSelect sb idx2 n b

      -- select the entire bitvector is the identity function
    | Just _ <- testEquality idx (knownNat :: NatRepr 0)
    , Just Refl <- testEquality n (bvWidth x) =
      return x

    | Just (BVShl w a b) <- asApp x
    , Just diff <- asBV b
    , Some diffRepr <- mkNatRepr (BV.asNatural diff)
    , Just LeqProof <- testLeq diffRepr idx = do
      Just LeqProof <- return $ testLeq (addNat (subNat idx diffRepr) n) w
      bvSelect sb (subNat idx diffRepr) n a

    | Just (BVShl _w _a b) <- asApp x
    , Just diff <- asBV b
    , Some diffRepr <- mkNatRepr (BV.asNatural diff)
    , Just LeqProof <- testLeq (addNat idx n) diffRepr =
      bvLit sb n (BV.zero n)

    | Just (BVAshr w a b) <- asApp x
    , Just diff <- asBV b
    , Some diffRepr <- mkNatRepr (BV.asNatural diff)
    , Just LeqProof <- testLeq (addNat (addNat idx diffRepr) n) w =
      bvSelect sb (addNat idx diffRepr) n a

    | Just (BVLshr w a b) <- asApp x
    , Just diff <- asBV b
    , Some diffRepr <- mkNatRepr (BV.asNatural diff)
    , Just LeqProof <- testLeq (addNat (addNat idx diffRepr) n) w =
      bvSelect sb (addNat idx diffRepr) n a

    | Just (BVLshr w _a b) <- asApp x
    , Just diff <- asBV b
    , Some diffRepr <- mkNatRepr (BV.asNatural diff)
    , Just LeqProof <- testLeq w (addNat idx diffRepr) =
      bvLit sb n (BV.zero n)

      -- select from a sign extension
    | Just (BVSext w b) <- asApp x = do
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (bvWidth b) w
      let ext = subNat w (bvWidth b)
      -- Add dynamic check
      Just LeqProof <- return $ isPosNat w
      Just LeqProof <- return $ isPosNat ext
      zeros <- minUnsignedBV sb ext
      ones  <- maxUnsignedBV sb ext
      c     <- bvIsNeg sb b
      hi    <- bvIte sb c ones zeros
      x'    <- bvConcat sb hi b
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (addNat idx n) (addNat ext (bvWidth b))
      bvSelect sb idx n x'

      -- select from a zero extension
    | Just (BVZext w b) <- asApp x = do
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (bvWidth b) w
      let ext = subNat w (bvWidth b)
      Just LeqProof <- return $ isPosNat w
      Just LeqProof <- return $ isPosNat ext
      hi    <- bvLit sb ext (BV.zero ext)
      x'    <- bvConcat sb hi b
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (addNat idx n) (addNat ext (bvWidth b))
      bvSelect sb idx n x'

      -- select is entirely within the less-significant bits of a concat
    | Just (BVConcat _w _a b) <- asApp x
    , Just LeqProof <- testLeq (addNat idx n) (bvWidth b) = do
      bvSelect sb idx n b

      -- select is entirely within the more-significant bits of a concat
    | Just (BVConcat _w a b) <- asApp x
    , Just LeqProof <- testLeq (bvWidth b) idx
    , Just LeqProof <- isPosNat idx
    , let diff = subNat idx (bvWidth b)
    , Just LeqProof <- testLeq (addNat diff n) (bvWidth a) = do
      bvSelect sb (subNat idx (bvWidth b)) n a

    -- when the selected region overlaps a concat boundary we have:
    --  select idx n (concat a b) =
    --      concat (select 0 n1 a) (select idx n2 b)
    --   where n1 + n2 = n and idx + n2 = width b
    --
    -- NB: this case must appear after the two above that check for selects
    --     entirely within the first or second arguments of a concat, otherwise
    --     some of the arithmetic checks below may fail
    | Just (BVConcat _w a b) <- asApp x = do
      Just LeqProof <- return $ testLeq idx (bvWidth b)
      let n2 = subNat (bvWidth b) idx
      Just LeqProof <- return $ testLeq n2 n
      let n1 = subNat n n2
      let z  = knownNat :: NatRepr 0

      Just LeqProof <- return $ isPosNat n1
      Just LeqProof <- return $ testLeq (addNat z n1) (bvWidth a)
      a' <- bvSelect sb z   n1 a

      Just LeqProof <- return $ isPosNat n2
      Just LeqProof <- return $ testLeq (addNat idx n2) (bvWidth b)
      b' <- bvSelect sb idx n2 b

      Just Refl <- return $ testEquality (addNat n1 n2) n
      bvConcat sb a' b'

    -- Truncate a weighted sum: Remove terms with coefficients that
    -- would become zero after truncation.
    --
    -- Truncation of w-bit words down to n bits respects congruence
    -- modulo 2^n. Furthermore, w-bit addition and multiplication also
    -- preserve congruence modulo 2^n. This means that it is sound to
    -- replace coefficients in a weighted sum with new masked ones
    -- that are congruent modulo 2^n: the final result after
    -- truncation will be the same.
    --
    -- NOTE: This case is carefully designed to preserve sharing. Only
    -- one App node (the SemiRingSum) is ever deconstructed. The
    -- 'traverseCoeffs' call does not touch any other App nodes inside
    -- the WeightedSum. Finally, we only reconstruct a new SemiRingSum
    -- App node in the event that one of the coefficients has changed;
    -- the writer monad tracks whether a change has occurred.
    | Just (SemiRingSum s) <- asApp x
    , SR.SemiRingBVRepr SR.BVArithRepr w <- WSum.sumRepr s
    , Just Refl <- testEquality idx (knownNat :: NatRepr 0) =
      do let mask = case testStrictLeq n w of
               Left LeqProof -> BV.zext w (BV.maxUnsigned n)
               Right Refl -> BV.maxUnsigned n
         let reduce i
               | i `BV.and` mask == BV.zero w = writer (BV.zero w, Any True)
               | otherwise                    = writer (i, Any False)
         let (s', Any changed) = runWriter $ WSum.traverseCoeffs reduce s
         x' <- if changed then sbMakeExpr sb (SemiRingSum s') else return x
         sbMakeExpr sb $ BVSelect idx n x'

{-  Avoid doing work that may lose sharing...

    -- Select from a weighted XOR: push down through the sum
    | Just (SemiRingSum s) <- asApp x
    , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.sumRepr s
    = do let mask = maxUnsigned n
         let shft = fromIntegral (natValue idx)
         s' <- WSum.transformSum (SR.SemiRingBVRepr SR.BVBitsRepr n)
                 (\c -> return ((c `Bits.shiftR` shft)  Bits..&. mask))
                 (bvSelect sb idx n)
                 s
         semiRingSum sb s'

    -- Select from a AND: push down through the AND
    | Just (SemiRingProd pd) <- asApp x
    , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr pd
    = do pd' <- WSum.prodEvalM
                   (bvAndBits sb)
                   (bvSelect sb idx n)
                   pd
         maybe (bvLit sb n (maxUnsigned n)) return pd'

    -- Select from an OR: push down through the OR
    | Just (BVOrBits pd) <- asApp x
    = do pd' <- WSum.prodEvalM
                   (bvOrBits sb)
                   (bvSelect sb idx n)
                   pd
         maybe (bvLit sb n 0) return pd'
-}

    -- Truncate from a unary bitvector
    | Just (BVUnaryTerm u) <- asApp x
    , Just Refl <- testEquality idx (knownNat @0) =
      bvUnary sb =<< UnaryBV.trunc sb u n

      -- if none of the above apply, produce a basic select term
    | otherwise = sbMakeExpr sb $ BVSelect idx n x

  testBitBV sym i y
    | i < 0 || i >= natValue (bvWidth y) =
      fail $ "Illegal bit index."

      -- Constant evaluation
    | Just yc <- asBV y
    , i <= fromIntegral (maxBound :: Int)
    = return $! backendPred sym (BV.testBit' (fromIntegral i) yc)

    | Just (BVZext _w y') <- asApp y
    = if i >= natValue (bvWidth y') then
        return $ falsePred sym
      else
        testBitBV sym i y'

    | Just (BVSext _w y') <- asApp y
    = if i >= natValue (bvWidth y') then
        testBitBV sym (natValue (bvWidth y') - 1) y'
      else
        testBitBV sym i y'

    | Just (BVFill _ p) <- asApp y
    = return p

    | Just b <- BVD.testBit (bvWidth y) (exprAbsValue y) i
    = return $! backendPred sym b

    | Just (BaseIte _ _ c a b) <- asApp y
    , isJust (asBV a) || isJust (asBV b) -- NB avoid losing sharing
    = do a' <- testBitBV sym i a
         b' <- testBitBV sym i b
         itePred sym c a' b'

{- These rewrites can sometimes yield significant simplifications, but
   also may lead to loss of sharing, so they are disabled...

    | Just ws <- asSemiRingSum (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth y)) y
    = let smul c x
           | Bits.testBit c (fromIntegral i) = testBitBV sym i x
           | otherwise                       = return (falsePred sym)
          cnst c = return $! backendPred sym (Bits.testBit c (fromIntegral i))
       in WSum.evalM (xorPred sym) smul cnst ws

    | Just pd <- asSemiRingProd (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth y)) y
    = fromMaybe (truePred sym) <$> WSum.prodEvalM (andPred sym) (testBitBV sym i) pd

    | Just (BVOrBits pd) <- asApp y
    = fromMaybe (falsePred sym) <$> WSum.prodEvalM (orPred sym) (testBitBV sym i) pd
-}

    | otherwise = sbMakeExpr sym $ BVTestBit i y

  bvFill sym w p
    | Just True  <- asConstantPred p = bvLit sym w (BV.maxUnsigned w)
    | Just False <- asConstantPred p = bvLit sym w (BV.zero w)
    | otherwise = sbMakeExpr sym $ BVFill w p

  bvIte sym c x y
    | Just (BVFill w px) <- asApp x
    , Just (BVFill _w py) <- asApp y =
      do z <- itePred sym c px py
         bvFill sym w z

    | Just (BVZext w  x') <- asApp x
    , Just (BVZext w' y') <- asApp y
    , Just Refl <- testEquality (bvWidth x') (bvWidth y')
    , Just Refl <- testEquality w w' =
      do z <- bvIte sym c x' y'
         bvZext sym w z

    | Just (BVSext w  x') <- asApp x
    , Just (BVSext w' y') <- asApp y
    , Just Refl <- testEquality (bvWidth x') (bvWidth y')
    , Just Refl <- testEquality w w' =
      do z <- bvIte sym c x' y'
         bvSext sym w z

    | Just (FloatToBinary fpp1 x') <- asApp x
    , Just (FloatToBinary fpp2 y') <- asApp y
    , Just Refl <- testEquality fpp1 fpp2 =
      floatToBinary sym =<< floatIte sym c x' y'

    | otherwise =
        do ut <- CFG.getOpt (sbUnaryThreshold sym)
           let ?unaryThreshold = fromInteger ut
           sbTryUnaryTerm sym
             (do ux <- asUnaryBV sym x
                 uy <- asUnaryBV sym y
                 return (UnaryBV.mux sym c ux uy))
             (case inSameBVSemiRing x y of
                Just (Some flv) ->
                  semiRingIte sym (SR.SemiRingBVRepr flv (bvWidth x)) c x y
                Nothing ->
                  mkIte sym c x y)

  bvEq sym x y
    | x == y = return $! truePred sym

    | Just (BVFill _ px) <- asApp x
    , Just (BVFill _ py) <- asApp y =
      eqPred sym px py

    | Just b <- BVD.eq (exprAbsValue x) (exprAbsValue y) = do
      return $! backendPred sym b

    -- Push some equalities under if/then/else
    | SemiRingLiteral _ _ _ <- x
    , Just (BaseIte _ _ c a b) <- asApp y
    , isJust (asBV a) || isJust (asBV b) -- avoid loss of sharing
    = join (itePred sym c <$> bvEq sym x a <*> bvEq sym x b)

    -- Push some equalities under if/then/else
    | Just (BaseIte _ _ c a b) <- asApp x
    , SemiRingLiteral _ _ _ <- y
    , isJust (asBV a) || isJust (asBV b) -- avoid loss of sharing
    = join (itePred sym c <$> bvEq sym a y <*> bvEq sym b y)

    | Just (Some flv) <- inSameBVSemiRing x y
    , let sr = SR.SemiRingBVRepr flv (bvWidth x)
    , (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
    , not (WSum.isZero sr z) =
        case (WSum.asConstant x', WSum.asConstant y') of
          (Just a, Just b) -> return $! backendPred sym (SR.eq sr a b)
          _ -> do xr <- semiRingSum sym x'
                  yr <- semiRingSum sym y'
                  sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min xr yr) (max xr yr)

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.eq sym ux uy
           | otherwise
           -> sbMakeExpr sym $ BaseEq (BaseBVRepr (bvWidth x)) (min x y) (max x y)

  bvSlt sym x y
    | Just xc <- asBV x
    , Just yc <- asBV y =
      return $! backendPred sym (BV.slt (bvWidth x) xc yc)
    | Just b <- BVD.slt (bvWidth x) (exprAbsValue x) (exprAbsValue y) =
      return $! backendPred sym b
    | x == y = return (falsePred sym)

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.slt sym ux uy
           | otherwise
           -> sbMakeExpr sym $ BVSlt x y

  bvUlt sym x y
    | Just xc <- asBV x
    , Just yc <- asBV y = do
      return $! backendPred sym (BV.ult xc yc)
    | Just b <- BVD.ult (exprAbsValue x) (exprAbsValue y) =
      return $! backendPred sym b
    | x == y =
      return $! falsePred sym

    | sr <- SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)
    , (z, x', y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
    , not (WSum.isZero sr z)
    , BVD.isUltSumCommonEquiv (WSum.sumAbsValue x') (WSum.sumAbsValue y') (WSum.sumAbsValue z) = do
      xr <- semiRingSum sym x'
      yr <- semiRingSum sym y'
      bvUlt sym xr yr

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.ult sym ux uy

           | otherwise
           -> sbMakeExpr sym $ BVUlt x y

  bvShl sym x y
   -- shift by 0 is the identity function
   | Just (BV.BV 0) <- asBV y
   = pure x

   -- shift by more than word width returns 0
   | let (lo, _hi) = BVD.ubounds (exprAbsValue y)
   , lo >= intValue (bvWidth x)
   = bvLit sym (bvWidth x) (BV.zero (bvWidth x))

   | Just xv <- asBV x, Just n <- asBV y
   = bvLit sym (bvWidth x) (BV.shl (bvWidth x) xv (BV.asNatural n))

   | otherwise
   = sbMakeExpr sym $ BVShl (bvWidth x) x y

  bvLshr sym x y
   -- shift by 0 is the identity function
   | Just (BV.BV 0) <- asBV y
   = pure x

   -- shift by more than word width returns 0
   | let (lo, _hi) = BVD.ubounds (exprAbsValue y)
   , lo >= intValue (bvWidth x)
   = bvLit sym (bvWidth x) (BV.zero (bvWidth x))

   | Just xv <- asBV x, Just n <- asBV y
   = bvLit sym (bvWidth x) $ BV.lshr (bvWidth x) xv (BV.asNatural n)

   | otherwise
   = sbMakeExpr sym $ BVLshr (bvWidth x) x y

  bvAshr sym x y
   -- shift by 0 is the identity function
   | Just (BV.BV 0) <- asBV y
   = pure x

   -- shift by more than word width returns either 0 (if x is nonnegative)
   -- or 1 (if x is negative)
   | let (lo, _hi) = BVD.ubounds (exprAbsValue y)
   , lo >= intValue (bvWidth x)
   = bvFill sym (bvWidth x) =<< bvIsNeg sym x

   | Just xv <- asBV x, Just n <- asBV y
   = bvLit sym (bvWidth x) $ BV.ashr (bvWidth x) xv (BV.asNatural n)

   | otherwise
   = sbMakeExpr sym $ BVAshr (bvWidth x) x y

  bvRol sym x y
   | Just xv <- asBV x, Just n <- asBV y
   = bvLit sym (bvWidth x) $ BV.rotateL (bvWidth x) xv (BV.asNatural n)

   | Just n <- asBV y
   , n `BV.urem` BV.width (bvWidth y) == BV.zero (bvWidth y)
   = return x

   | Just (BVRol w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvAdd sym n y
        bvRol sym x' z

   | Just (BVRol w x' n) <- asApp x
   = do wbv <- bvLit sym w (BV.width w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' y'
        bvRol sym x' z

   | Just (BVRor w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvSub sym n y
        bvRor sym x' z

   | Just (BVRor w x' n) <- asApp x
   = do wbv <- bvLit sym w (BV.width w)
        y' <- bvUrem sym y wbv
        n' <- bvUrem sym n wbv
        z <- bvAdd sym n' =<< bvSub sym wbv y'
        bvRor sym x' z

   | otherwise
   = let w = bvWidth x in
     sbMakeExpr sym $ BVRol w x y

  bvRor sym x y
   | Just xv <- asBV x, Just n <- asBV y
   = bvLit sym (bvWidth x) $ BV.rotateR (bvWidth x) xv (BV.asNatural n)

   | Just n <- asBV y
   , n `BV.urem` BV.width (bvWidth y) == BV.zero (bvWidth y)
   = return x

   | Just (BVRor w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvAdd sym n y
        bvRor sym x' z

   | Just (BVRor w x' n) <- asApp x
   = do wbv <- bvLit sym w (BV.width w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' y'
        bvRor sym x' z

   | Just (BVRol w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvSub sym n y
        bvRol sym x' z

   | Just (BVRol w x' n) <- asApp x
   = do wbv <- bvLit sym w (BV.width w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' =<< bvSub sym wbv y'
        bvRol sym x' z

   | otherwise
   = let w = bvWidth x in
     sbMakeExpr sym $ BVRor w x y

  bvZext sym w x
    | Just xv <- asBV x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvLit sym w (BV.zext w xv)

      -- Concatenate unsign extension.
    | Just (BVZext _ y) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym $ BVZext w y

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.uext u w

    | otherwise = do
      pmo <- CFG.getOpt (sbPushMuxOps sym)
      if | pmo
         , Just (BaseIte _ _ c a b) <- asApp x
         , Just a_bv <- asBV a
         , Just b_bv <- asBV b -> do
             Just LeqProof <- return $ isPosNat w
             a' <- bvLit sym w $ BV.zext w a_bv
             b' <- bvLit sym w $ BV.zext w b_bv
             bvIte sym c a' b'

         | otherwise -> do
             Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
             sbMakeExpr sym $ BVZext w x

  bvSext sym w x
    | Just xv <- asBV x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvLit sym w (BV.sext (bvWidth x) w xv)

      -- Concatenate sign extension.
    | Just (BVSext _ y) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym (BVSext w y)

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.sext u w

    | otherwise = do
      pmo <- CFG.getOpt (sbPushMuxOps sym)
      if | pmo
         , Just (BaseIte _ _ c a b) <- asApp x
         , Just a_bv <- asBV a
         , Just b_bv <- asBV b -> do
             Just LeqProof <- return $ isPosNat w
             a' <- bvLit sym w $ BV.sext (bvWidth x) w a_bv
             b' <- bvLit sym w $ BV.sext (bvWidth x) w b_bv
             bvIte sym c a' b'

         | otherwise -> do
             Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
             sbMakeExpr sym (BVSext w x)

  bvXorBits sym x y
    | x == y = bvLit sym (bvWidth x) (BV.zero (bvWidth x))  -- special case: x `xor` x = 0
    | otherwise
    = let sr = SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x)
       in semiRingAdd sym sr x y

  bvAndBits sym x y
    | x == y = return x -- Special case: idempotency of and

    | Just (BVOrBits _ bs) <- asApp x
    , bvOrContains y bs
    = return y -- absorption law

    | Just (BVOrBits _ bs) <- asApp y
    , bvOrContains x bs
    = return x -- absorption law

    | otherwise
    = do pmo <- CFG.getOpt (sbPushMuxOps sym)
         if | pmo
            , Just (BaseIte _ _ c a b) <- asApp x
            , Just a_bv <- asBV a
            , Just b_bv <- asBV b
            , Just y_bv <- asBV y -> do
                a' <- bvLit sym (bvWidth x) $ BV.and a_bv y_bv
                b' <- bvLit sym (bvWidth x) $ BV.and b_bv y_bv
                bvIte sym c a' b'

            | pmo
            , Just (BaseIte _ _ c a b) <- asApp y
            , Just a_bv <- asBV a
            , Just b_bv <- asBV b
            , Just x_bv <- asBV x -> do
                a' <- bvLit sym (bvWidth x) $ BV.and x_bv a_bv
                b' <- bvLit sym (bvWidth x) $ BV.and x_bv b_bv
                bvIte sym c a' b'

            | otherwise
            -> let sr = SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x)
                in semiRingMul sym sr x y

  -- XOR by the all-1 constant of the bitwise semiring.
  -- This is equivalant to negation
  bvNotBits sym x
    | Just xv <- asBV x
    = bvLit sym (bvWidth x) $ xv `BV.xor` (BV.maxUnsigned (bvWidth x))

    | otherwise
    = do pmo <- CFG.getOpt (sbPushMuxOps sym)
         if | pmo
            , Just (BaseIte _ _ c a b) <- asApp x
            , Just a_bv <- asBV a
            , Just b_bv <- asBV b -> do
                a' <- bvLit sym (bvWidth x) $ BV.complement (bvWidth x) a_bv
                b' <- bvLit sym (bvWidth x) $ BV.complement (bvWidth x) b_bv
                bvIte sym c a' b'
            | otherwise ->
                let sr = (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x))
                 in semiRingSum sym $ WSum.addConstant sr (asWeightedSum sr x) (BV.maxUnsigned (bvWidth x))

  bvOrBits sym x y =
    case (asBV x, asBV y) of
      (Just xv, Just yv) -> bvLit sym (bvWidth x) (xv `BV.or` yv)
      (Just xv , _)
        | xv == BV.zero (bvWidth x) -> return y
        | xv == BV.maxUnsigned (bvWidth x) -> return x
      (_, Just yv)
        | yv == BV.zero (bvWidth y) -> return x
        | yv == BV.maxUnsigned (bvWidth x) -> return y

      _
        | x == y
        -> return x -- or is idempotent

        | Just (SemiRingProd xs) <- asApp x
        , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr xs
        , WSum.prodContains xs y
        -> return y   -- absorption law

        | Just (SemiRingProd ys) <- asApp y
        , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr ys
        , WSum.prodContains ys x
        -> return x   -- absorption law

        | Just (BVOrBits w xs) <- asApp x
        , Just (BVOrBits _ ys) <- asApp y
        -> sbMakeExpr sym $ BVOrBits w $ bvOrUnion xs ys

        | Just (BVOrBits w xs) <- asApp x
        -> sbMakeExpr sym $ BVOrBits w $ bvOrInsert y xs

        | Just (BVOrBits w ys) <- asApp y
        -> sbMakeExpr sym $ BVOrBits w $ bvOrInsert x ys

        -- (or (shl x n) (zext w y)) is equivalent to (concat (trunc (w - n) x) y) when n is
        -- the number of bits of y. Notice that the low bits of a shl expression are 0 and
        -- the high bits of a zext expression are 0, thus the or expression is equivalent to
        -- the concatenation between the high bits of the shl expression and the low bits of
        -- the zext expression.
        | Just (BVShl w x' n) <- asApp x
        , Just (BVZext _ lo) <- asApp y
        , Just ni <- BV.asUnsigned <$> asBV n
        , intValue (bvWidth lo) == ni
        , Just LeqProof <- testLeq (bvWidth lo) w -- dynamic check for GHC typechecker
        , w' <- subNat w (bvWidth lo)
        , Just LeqProof <- testLeq (knownNat @1) w' -- dynamic check for GHC typechecker
        , Just LeqProof <- testLeq (addNat w' (knownNat @1)) w -- dynamic check for GHC typechecker
        , Just Refl <- testEquality w (addNat w' (bvWidth lo)) -- dynamic check for GHC typechecker
        -> do
          hi <- bvTrunc sym w' x'
          bvConcat sym hi lo
        | Just (BVShl w y' n) <- asApp y
        , Just (BVZext _ lo) <- asApp x
        , Just ni <- BV.asUnsigned <$> asBV n
        , intValue (bvWidth lo) == ni
        , Just LeqProof <- testLeq (bvWidth lo) w -- dynamic check for GHC typechecker
        , w' <- subNat w (bvWidth lo)
        , Just LeqProof <- testLeq (knownNat @1) w' -- dynamic check for GHC typechecker
        , Just LeqProof <- testLeq (addNat w' (knownNat @1)) w -- dynamic check for GHC typechecker
        , Just Refl <- testEquality w (addNat w' (bvWidth lo)) -- dynamic check for GHC typechecker
        -> do
          hi <- bvTrunc sym w' y'
          bvConcat sym hi lo

        | otherwise
        -> sbMakeExpr sym $ BVOrBits (bvWidth x) $ bvOrInsert x $ bvOrSingleton y

  bvAdd sym x y = semiRingAdd sym sr x y
     where sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)

  bvMul sym x y = semiRingMul sym sr x y
     where sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)

  bvNeg sym x
    | Just xv <- asBV x = bvLit sym (bvWidth x) (BV.negate (bvWidth x) xv)
    | otherwise = do
        pmo <- CFG.getOpt (sbPushMuxOps sym)
        if | pmo
           , Just (BaseIte _ _ c a b) <- asApp x
           , Just a_bv <- asBV a
           , Just b_bv <- asBV b -> do
               a' <- bvLit sym (bvWidth x) $ BV.negate (bvWidth x) a_bv
               b' <- bvLit sym (bvWidth x) $ BV.negate (bvWidth x) b_bv
               bvIte sym c a' b'
           | otherwise -> do
               ut <- CFG.getOpt (sbUnaryThreshold sym)
               let ?unaryThreshold = fromInteger ut
               sbTryUnaryTerm sym
                 (do ux <- asUnaryBV sym x
                     Just (UnaryBV.neg sym ux))
                 (do let sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)
                     scalarMul sym sr (BV.mkBV (bvWidth x) (-1)) x)

  bvIsNonzero sym x
    | Just (BaseIte _ _ p t f) <- asApp x
    , isJust (asBV t) || isJust (asBV f) -- NB, avoid losing possible sharing
    = do  t' <- bvIsNonzero sym t
          f' <- bvIsNonzero sym f
          itePred sym p t' f'
    | Just (BVConcat _ a b) <- asApp x
    , isJust (asBV a) || isJust (asBV b) -- NB, avoid losing possible sharing
    =  do pa <- bvIsNonzero sym a
          pb <- bvIsNonzero sym b
          orPred sym pa pb
    | Just (BVZext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (BVSext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (BVFill _ p) <- asApp x =
          return p
    | Just (BVUnaryTerm ubv) <- asApp x =
          UnaryBV.sym_evaluate
            (\i -> return $! backendPred sym (i/=0))
            (itePred sym)
            ubv
    | otherwise = do
          let w = bvWidth x
          zro <- bvLit sym w (BV.zero w)
          notPred sym =<< bvEq sym x zro

  bvUdiv = bvBinDivOp (const BV.uquot) BVUdiv
  bvUrem sym x y
    | Just True <- BVD.ult (exprAbsValue x) (exprAbsValue y) = return x
    | otherwise = bvBinDivOp (const BV.urem) BVUrem sym x y
  bvSdiv = bvBinDivOp BV.squot BVSdiv
  bvSrem = bvBinDivOp BV.srem BVSrem

  bvPopcount sym x
    | Just xv <- asBV x = bvLit sym w (BV.popCount xv)
    | otherwise = sbMakeExpr sym $ BVPopcount w x
   where w = bvWidth x

  bvCountTrailingZeros sym x
    | Just xv <- asBV x = bvLit sym w (BV.ctz w xv)
    | otherwise = sbMakeExpr sym $ BVCountTrailingZeros w x
   where w = bvWidth x

  bvCountLeadingZeros sym x
    | Just xv <- asBV x = bvLit sym w (BV.clz w xv)
    | otherwise = sbMakeExpr sym $ BVCountLeadingZeros w x
   where w = bvWidth x

  mkStruct sym args = do
    sbMakeExpr sym $ StructCtor (fmapFC exprType args) args

  structField sym s i
    | Just (StructCtor _ args) <- asApp s = return $! args Ctx.! i
    | otherwise = do
      case exprType s of
        BaseStructRepr flds ->
          sbMakeExpr sym $ StructField s i (flds Ctx.! i)

  structIte sym p x y
    | Just True  <- asConstantPred p = return x
    | Just False <- asConstantPred p = return y
    | x == y                         = return x
    | otherwise                      = mkIte sym p x y

  --------------------------------------------------------------------
  -- String operations

  stringEmpty sym si = stringLit sym (stringLitEmpty si)

  stringLit sym s =
    do l <- curProgramLoc sym
       return $! StringExpr s l

  stringEq sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (isJust (testEquality x' y'))
  stringEq sym x y
    = sbMakeExpr sym $ BaseEq (BaseStringRepr (stringInfo x)) x y

  stringIte _sym c x y
    | Just c' <- asConstantPred c
    = if c' then return x else return y
  stringIte _sym _c x y
    | Just x' <- asString x
    , Just y' <- asString y
    , isJust (testEquality x' y')
    = return x
  stringIte sym c x y
    = mkIte sym c x y

  stringIndexOf sym x y k
    | Just x' <- asString x
    , Just y' <- asString y
    , Just k' <- asInteger k
    = intLit sym $! stringLitIndexOf x' y' k'
  stringIndexOf sym x y k
    = sbMakeExpr sym $ StringIndexOf x y k

  stringContains sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitContains x' y')
    | Just b <- stringAbsContains (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b
    | otherwise
    = sbMakeExpr sym $ StringContains x y

  stringIsPrefixOf sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitIsPrefixOf x' y')

    | Just b <- stringAbsIsPrefixOf (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b

    | otherwise
    = sbMakeExpr sym $ StringIsPrefixOf x y

  stringIsSuffixOf sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitIsSuffixOf x' y')

    | Just b <- stringAbsIsSuffixOf (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b

    | otherwise
    = sbMakeExpr sym $ StringIsSuffixOf x y

  stringSubstring sym x off len
    | Just x' <- asString x
    , Just off' <- asInteger off
    , Just len' <- asInteger len
    = stringLit sym $! stringLitSubstring x' off' len'

    | otherwise
    = sbMakeExpr sym $ StringSubstring (stringInfo x) x off len

  stringConcat sym x y
    | Just x' <- asString x, stringLitNull x'
    = return y

    | Just y' <- asString y, stringLitNull y'
    = return x

    | Just x' <- asString x
    , Just y' <- asString y
    = stringLit sym (x' <> y')

    | Just (StringAppend si xs) <- asApp x
    , Just (StringAppend _  ys) <- asApp y
    = sbMakeExpr sym $ StringAppend si (SSeq.append xs ys)

    | Just (StringAppend si xs) <- asApp x
    = sbMakeExpr sym $ StringAppend si (SSeq.append xs (SSeq.singleton si y))

    | Just (StringAppend si ys) <- asApp y
    = sbMakeExpr sym $ StringAppend si (SSeq.append (SSeq.singleton si x) ys)

    | otherwise
    = let si = stringInfo x in
      sbMakeExpr sym $ StringAppend si (SSeq.append (SSeq.singleton si x) (SSeq.singleton si y))

  stringLength sym x
    | Just x' <- asString x
    = intLit sym (stringLitLength x')

    | Just (StringAppend _si xs) <- asApp x
    = do let f sm (SSeq.StringSeqLiteral l) = intAdd sym sm =<< intLit sym (stringLitLength l)
             f sm (SSeq.StringSeqTerm t)    = intAdd sym sm =<< sbMakeExpr sym (StringLength t)
         z  <- intLit sym 0
         foldM f z (SSeq.toList xs)

    | otherwise
    = sbMakeExpr sym $ StringLength x

  --------------------------------------------------------------------
  -- Symbolic array operations

  constantArray sym idxRepr v =
    sbMakeExpr sym $ ConstantArray idxRepr (exprType v) v

  arrayFromFn sym fn = do
    sbNonceExpr sym $ ArrayFromFn fn

  arrayMap sym f arrays
      -- Cancel out integerToReal (realToInteger a)
    | Just IntegerToRealFn  <- asMatlabSolverFn f
    , Just (MapOverArrays g _ args) <- asNonceApp (unwrapArrayResult (arrays^._1))
    , Just RealToIntegerFn <- asMatlabSolverFn g =
      return $! unwrapArrayResult (args^._1)
      -- Cancel out realToInteger (integerToReal a)
    | Just RealToIntegerFn  <- asMatlabSolverFn f
    , Just (MapOverArrays g _ args) <- asNonceApp (unwrapArrayResult (arrays^._1))
    , Just IntegerToRealFn <- asMatlabSolverFn g =
      return $! unwrapArrayResult (args^._1)

    -- When the array is an update of concrete entries, map over the entries.
    | s <- concreteArrayEntries arrays
    , not (Set.null s) = do
        -- Distribute over base values.
        --
        -- The underlyingArrayMapElf function strings a top-level arrayMap value.
        --
        -- It is ok because we don't care what the value of base is at any index
        -- in s.
        base <- arrayMap sym f (fmapFC underlyingArrayMapExpr arrays)
        BaseArrayRepr _ ret <- return (exprType base)

        -- This lookups a given index in an array used as an argument.
        let evalArgs :: Ctx.Assignment IndexLit (idx ::> itp)
                        -- ^ A representatio of the concrete index (if defined).
                        -> Ctx.Assignment (Expr t)  (idx ::> itp)
                           -- ^ The index to use.
                        -> ArrayResultWrapper (Expr t) (idx ::> itp) d
                           -- ^ The array to get the value at.
                        -> IO (Expr t d)
            evalArgs const_idx sym_idx a = do
              sbConcreteLookup sym (unwrapArrayResult a) (Just const_idx) sym_idx
        let evalIndex :: ExprSymFn t ctx ret
                      -> Ctx.Assignment (ArrayResultWrapper (Expr t) (i::>itp)) ctx
                      -> Ctx.Assignment IndexLit (i::>itp)
                      -> IO (Expr t ret)
            evalIndex g arrays0 const_idx = do
              sym_idx <- traverseFC (indexLit sym) const_idx
              applySymFn sym g =<< traverseFC (evalArgs const_idx sym_idx) arrays0
        m <- AUM.fromAscList ret <$> mapM (\k -> (k,) <$> evalIndex f arrays k) (Set.toAscList s)
        arrayUpdateAtIdxLits sym m base
      -- When entries are constants, then just evaluate constant.
    | Just cns <-  traverseFC (\a -> asConstantArray (unwrapArrayResult a)) arrays = do
      r <- betaReduce sym f cns
      case exprType (unwrapArrayResult (Ctx.last arrays)) of
        BaseArrayRepr idxRepr _ -> do
          constantArray sym idxRepr r

    | otherwise = do
      let idx = arrayResultIdxType (exprType (unwrapArrayResult (Ctx.last arrays)))
      sbNonceExpr sym $ MapOverArrays f idx arrays

  arrayUpdate sym arr i v
      -- Update at concrete index.
    | Just ci <- asConcreteIndices i =
      case asApp arr of
        Just (ArrayMap idx tp m def) -> do
          let new_map =
                case asApp def of
                  Just (ConstantArray _ _ cns) | v == cns -> AUM.delete ci m
                  _ -> AUM.insert tp ci v m
          sbMakeExpr sym $ ArrayMap idx tp new_map def
        _ -> do
          let idx = fmapFC exprType  i
          let bRepr = exprType v
          let new_map = AUM.singleton bRepr ci v
          sbMakeExpr sym $ ArrayMap idx bRepr new_map arr
    | otherwise = do
      let bRepr = exprType v
      sbMakeExpr sym (UpdateArray bRepr (fmapFC exprType i)  arr i v)

  arrayLookup sym arr idx =
    sbConcreteLookup sym arr (asConcreteIndices idx) idx

  arrayCopy sym dest_arr dest_idx src_arr src_idx len = case exprType dest_arr of
    (BaseArrayRepr _ a_repr) -> do
      dest_end_idx <- bvAdd sym dest_idx len
      src_end_idx <- bvAdd sym src_idx len
      sbMakeExpr sym (CopyArray (bvWidth dest_idx) a_repr dest_arr dest_idx src_arr src_idx len dest_end_idx src_end_idx)

  arraySet sym arr idx val len = do
    end_idx <- bvAdd sym idx len
    sbMakeExpr sym (SetArray (bvWidth idx) (exprType val) arr idx val len end_idx)

  arrayRangeEq sym x_arr x_idx y_arr y_idx len = case exprType x_arr of
    (BaseArrayRepr _ a_repr) -> do
      x_end_idx <- bvAdd sym x_idx len
      y_end_idx <- bvAdd sym y_idx len
      sbMakeExpr sym (EqualArrayRange (bvWidth x_idx) a_repr x_arr x_idx y_arr y_idx len x_end_idx y_end_idx)

  -- | Create an array from a map of concrete indices to values.
  arrayUpdateAtIdxLits sym m def_map = do
    BaseArrayRepr idx_tps baseRepr <- return $ exprType def_map
    let new_map
          | Just (ConstantArray _ _ default_value) <- asApp def_map =
            AUM.filter (/= default_value) m
          | otherwise = m
    if AUM.null new_map then
      return def_map
     else
      sbMakeExpr sym $ ArrayMap idx_tps baseRepr new_map def_map

  arrayIte sym p x y = do
    pmo <- CFG.getOpt (sbPushMuxOps sym)
    if   -- Extract all concrete updates out.
       | not pmo
       , ArrayMapView mx x' <- viewArrayMap x
       , ArrayMapView my y' <- viewArrayMap y
       , not (AUM.null mx) || not (AUM.null my) -> do
         case exprType x of
           BaseArrayRepr idxRepr bRepr -> do
             let both_fn _ u v = baseTypeIte sym p u v
                 left_fn idx u = do
                   v <- sbConcreteLookup sym y' (Just idx) =<< symbolicIndices sym idx
                   both_fn idx u v
                 right_fn idx v = do
                   u <- sbConcreteLookup sym x' (Just idx) =<< symbolicIndices sym idx
                   both_fn idx u v
             mz <- AUM.mergeM bRepr both_fn left_fn right_fn mx my
             z' <- arrayIte sym p x' y'

             sbMakeExpr sym $ ArrayMap idxRepr bRepr mz z'

       | otherwise -> mkIte sym p x y

  arrayEq sym x y
    | x == y =
      return $! truePred sym
    | otherwise =
      sbMakeExpr sym $! BaseEq (exprType x) x y

  arrayTrueOnEntries sym f a
    | Just True <- exprAbsValue a =
      return $ truePred sym
    | Just (IndicesInRange _ bnds) <- asMatlabSolverFn f
    , Just v <- asIntBounds bnds = do
      let h :: Expr t (BaseArrayType (i::>it) BaseBoolType)
            -> BoolExpr t
            -> Ctx.Assignment (Expr t) (i::>it)
            -> IO (BoolExpr t)
          h a0 p i = andPred sym p =<< arrayLookup sym a0 i
      foldIndicesInRangeBounds sym (h a) (truePred sym) v

    | otherwise =
      sbNonceExpr sym $! ArrayTrueOnEntries f a

  ----------------------------------------------------------------------
  -- Lossless (injective) conversions

  integerToReal sym x
    | SemiRingLiteral SR.SemiRingIntegerRepr i l <- x = return $! SemiRingLiteral SR.SemiRingRealRepr (toRational i) l
    | Just (RealToInteger y) <- asApp x = return y
    | otherwise  = sbMakeExpr sym (IntegerToReal x)

  realToInteger sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $! SemiRingLiteral SR.SemiRingIntegerRepr (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | otherwise =
      sbMakeExpr sym (RealToInteger x)

  bvToInteger sym x
    | Just xv <- asBV x =
      intLit sym (BV.asUnsigned xv)
      -- bvToInteger (integerToBv x w) == mod x (2^w)
    | Just (IntegerToBV xi w) <- asApp x =
      intMod sym xi =<< intLit sym (2^natValue w)
    | otherwise =
      sbMakeExpr sym (BVToInteger x)

  sbvToInteger sym x
    | Just xv <- asBV x =
      intLit sym (BV.asSigned (bvWidth x) xv)
      -- sbvToInteger (integerToBv x w) == mod (x + 2^(w-1)) (2^w) - 2^(w-1)
    | Just (IntegerToBV xi w) <- asApp x =
      do halfmod <- intLit sym (2 ^ (natValue w - 1))
         modulus <- intLit sym (2 ^ natValue w)
         x'      <- intAdd sym xi halfmod
         z       <- intMod sym x' modulus
         intSub sym z halfmod
    | otherwise =
      sbMakeExpr sym (SBVToInteger x)

  predToBV sym p w
    | Just b <- asConstantPred p =
        if b then bvLit sym w (BV.one w) else bvLit sym w (BV.zero w)
    | otherwise =
       case testNatCases w (knownNat @1) of
         NatCaseEQ   -> sbMakeExpr sym (BVFill (knownNat @1) p)
         NatCaseGT LeqProof -> bvZext sym w =<< sbMakeExpr sym (BVFill (knownNat @1) p)
         NatCaseLT LeqProof -> fail "impossible case in predToBV"

  integerToBV sym xr w
    | SemiRingLiteral SR.SemiRingIntegerRepr i _ <- xr =
      bvLit sym w (BV.mkBV w i)

    | Just (BVToInteger r) <- asApp xr =
      case testNatCases (bvWidth r) w of
        NatCaseLT LeqProof -> bvZext sym w r
        NatCaseEQ   -> return r
        NatCaseGT LeqProof -> bvTrunc sym w r

    | Just (SBVToInteger r) <- asApp xr =
      case testNatCases (bvWidth r) w of
        NatCaseLT LeqProof -> bvSext sym w r
        NatCaseEQ   -> return r
        NatCaseGT LeqProof -> bvTrunc sym w r

    | otherwise =
      sbMakeExpr sym (IntegerToBV xr w)

  realRound sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (roundAway r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (RoundReal x)

  realRoundEven sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (round r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (RoundEvenReal x)

  realFloor sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (FloorReal x)

  realCeil sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (ceiling r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (CeilReal x)

  ----------------------------------------------------------------------
  -- Real operations

  realLit sb r = do
    l <- curProgramLoc sb
    return (SemiRingLiteral SR.SemiRingRealRepr r l)

  realZero = sbZero

  realEq sym x y
      -- Use range check
    | Just b <- ravCheckEq (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to integer equality, when possible
    | Just (IntegerToReal xi) <- asApp x
    , Just (IntegerToReal yi) <- asApp y
    = intEq sym xi yi

    | Just (IntegerToReal xi) <- asApp x
    , SemiRingLiteral SR.SemiRingRealRepr yr _ <- y
    = if denominator yr == 1
         then intEq sym xi =<< intLit sym (numerator yr)
         else return (falsePred sym)

    | SemiRingLiteral SR.SemiRingRealRepr xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = if denominator xr == 1
         then intEq sym yi =<< intLit sym (numerator xr)
         else return (falsePred sym)

    | otherwise
    = semiRingEq sym SR.SemiRingRealRepr (realEq sym) x y

  realLe sym x y
      -- Use range check
    | Just b <- ravCheckLe (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to integer inequality, when possible
    | Just (IntegerToReal xi) <- asApp x
    , Just (IntegerToReal yi) <- asApp y
    = intLe sym xi yi

      -- if the upper range is a constant, do an integer comparison
      -- with @floor(y)@
    | Just (IntegerToReal xi) <- asApp x
    , SemiRingLiteral SR.SemiRingRealRepr yr _ <- y
    = join (intLe sym <$> pure xi <*> intLit sym (floor yr))

      -- if the lower range is a constant, do an integer comparison
      -- with @ceiling(x)@
    | SemiRingLiteral SR.SemiRingRealRepr xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = join (intLe sym <$> intLit sym (ceiling xr) <*> pure yi)

    | otherwise
    = semiRingLe sym SR.OrderedSemiRingRealRepr (realLe sym) x y

  realIte sym c x y = semiRingIte sym SR.SemiRingRealRepr c x y

  realNeg sym x = scalarMul sym SR.SemiRingRealRepr (-1) x

  realAdd sym x y = semiRingAdd sym SR.SemiRingRealRepr x y

  realMul sym x y = semiRingMul sym SR.SemiRingRealRepr x y

  realDiv sym x y
    | Just 0 <- asRational x =
      return x
    | Just xd <- asRational x, Just yd <- asRational y, yd /= 0 = do
      realLit sym (xd / yd)
      -- Handle division by a constant.
    | Just yd <- asRational y, yd /= 0 = do
      scalarMul sym SR.SemiRingRealRepr (1 / yd) x
    | otherwise =
      sbMakeExpr sym $ RealDiv x y

  isInteger sb x
    | Just r <- asRational x = return $ backendPred sb (denominator r == 1)
    | Just b <- ravIsInteger (exprAbsValue x) = return $ backendPred sb b
    | otherwise = sbMakeExpr sb $ RealIsInteger x

  realSqrt sym x = do
    let sqrt_dbl :: Double -> Double
        sqrt_dbl = sqrt
    case x of
      SemiRingLiteral SR.SemiRingRealRepr r _
        | r < 0 -> sbMakeExpr sym (RealSqrt x)
        | Just w <- tryRationalSqrt r -> realLit sym w
        | sbFloatReduce sym -> realLit sym (toRational (sqrt_dbl (fromRational r)))
      _ -> sbMakeExpr sym (RealSqrt x)

  realSpecialFunction sym fn Empty
    | sbFloatReduce sym =
        case fn of
          SFn.Pi -> realLit sym (toRational (pi :: Double))
          -- TODO, other constants

          _ -> sbMakeExpr sym (RealSpecialFunction fn (SFn.SpecialFnArgs Empty))

  realSpecialFunction sym fn args@(Empty :> SFn.SpecialFnArg x)
    | Just c <- asRational x =
        case fn of
          SFn.Sin
            | c == 0 -> realLit sym 0
            | sbFloatReduce sym -> realLit sym (toRational (sin (toDouble c)))
          SFn.Cos
            | c == 0 -> realLit sym 1
            | sbFloatReduce sym -> realLit sym (toRational (cos (toDouble c)))
          SFn.Sinh
            | c == 0 -> realLit sym 0
            | sbFloatReduce sym -> realLit sym (toRational (sinh (toDouble c)))
          SFn.Cosh
            | c == 0 -> realLit sym 1
            | sbFloatReduce sym -> realLit sym (toRational (cosh (toDouble c)))
          SFn.Exp
            | c == 0 -> realLit sym 1
            | sbFloatReduce sym -> realLit sym (toRational (exp (toDouble c)))
          SFn.Log
            | c > 0, sbFloatReduce sym -> realLit sym (toRational (log (toDouble c)))
          _ -> sbMakeExpr sym (RealSpecialFunction fn (SFn.SpecialFnArgs args))

  realSpecialFunction sym fn args@(Empty :> SFn.SpecialFnArg x :> SFn.SpecialFnArg y)
    | Just xc <- asRational x,
      Just yc <- asRational y =
        case fn of
          SFn.Arctan2
            | sbFloatReduce sym -> realLit sym (toRational (atan2 (toDouble xc) (toDouble yc)))
          SFn.Pow
            | yc == 0 -> realLit sym 1
            | sbFloatReduce sym ->
              realLit sym (toRational (toDouble xc ** toDouble yc))
          _ -> sbMakeExpr sym (RealSpecialFunction fn (SFn.SpecialFnArgs args))

  realSpecialFunction sym fn args = sbMakeExpr sym (RealSpecialFunction fn (SFn.SpecialFnArgs args))

  ----------------------------------------------------------------------
  -- IEEE-754 floating-point operations

  floatLit sym fpp f =
    do l <- curProgramLoc sym
       return $! FloatExpr fpp f l

  floatPZero sym fpp = floatLit sym fpp BF.bfPosZero
  floatNZero sym fpp = floatLit sym fpp BF.bfNegZero
  floatNaN   sym fpp = floatLit sym fpp BF.bfNaN
  floatPInf  sym fpp = floatLit sym fpp BF.bfPosInf
  floatNInf  sym fpp = floatLit sym fpp BF.bfNegInf

  floatNeg sym (FloatExpr fpp x _) = floatLit sym fpp (BF.bfNeg x)
  floatNeg sym x = floatIEEEArithUnOp FloatNeg sym x

  floatAbs sym (FloatExpr fpp x _) = floatLit sym fpp (BF.bfAbs x)
  floatAbs sym x = floatIEEEArithUnOp FloatAbs sym x

  floatSqrt sym r (FloatExpr fpp x _) =
    floatLit sym fpp (bfStatus (BF.bfSqrt (fppOpts fpp r) x))
  floatSqrt sym r x = floatIEEEArithUnOpR FloatSqrt sym r x

  floatAdd sym r (FloatExpr fpp x _) (FloatExpr _ y _) =
    floatLit sym fpp (bfStatus (BF.bfAdd (fppOpts fpp r) x y))
  floatAdd sym r x y = floatIEEEArithBinOpR FloatAdd sym r x y

  floatSub sym r (FloatExpr fpp x _) (FloatExpr _ y _) =
    floatLit sym fpp (bfStatus (BF.bfSub (fppOpts fpp r) x y ))
  floatSub sym r x y = floatIEEEArithBinOpR FloatSub sym r x y

  floatMul sym r (FloatExpr fpp x _) (FloatExpr _ y _) =
    floatLit sym fpp (bfStatus (BF.bfMul (fppOpts fpp r) x y))
  floatMul sym r x y = floatIEEEArithBinOpR FloatMul sym r x y

  floatDiv sym r (FloatExpr fpp x _) (FloatExpr _ y _) =
    floatLit sym fpp (bfStatus (BF.bfDiv (fppOpts fpp r) x y))
  floatDiv sym r x y = floatIEEEArithBinOpR FloatDiv sym r x y

  floatRem sym (FloatExpr fpp x _) (FloatExpr _ y _) =
    floatLit sym fpp (bfStatus (BF.bfRem (fppOpts fpp RNE) x y))
  floatRem sym x y = floatIEEEArithBinOp FloatRem sym x y

  floatFMA sym r (FloatExpr fpp x _) (FloatExpr _ y _) (FloatExpr _ z _) =
    floatLit sym fpp (bfStatus (BF.bfFMA (fppOpts fpp r) x y z))
  floatFMA sym r x y z =
    let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ FloatFMA fpp r x y z

  floatEq sym (FloatExpr _ x _) (FloatExpr _ y _) =
    pure . backendPred sym $! (BF.bfCompare x y == EQ)
  floatEq sym x y
    | x == y = return $! truePred sym
    | otherwise = floatIEEELogicBinOp (BaseEq (exprType x)) sym x y

  floatNe sym x y = notPred sym =<< floatEq sym x y

  floatFpEq sym (FloatExpr _ x _) (FloatExpr _ y _) =
    pure . backendPred sym $! (x == y)
  floatFpEq sym x y
    | x == y = notPred sym =<< floatIsNaN sym x
    | otherwise = floatIEEELogicBinOp FloatFpEq sym x y

  floatLe sym (FloatExpr _ x _) (FloatExpr _ y _) =
    pure . backendPred sym $! (x <= y)
  floatLe sym x y
    | x == y = notPred sym =<< floatIsNaN sym x
    | otherwise = floatIEEELogicBinOp FloatLe sym x y

  floatLt sym (FloatExpr _ x _) (FloatExpr _ y _) =
    pure . backendPred sym $! (x < y)
  floatLt sym x y
    | x == y = return $ falsePred sym
    | otherwise = floatIEEELogicBinOp FloatLt sym x y

  floatGe sym x y = floatLe sym y x
  floatGt sym x y = floatLt sym y x
  floatIte sym c x y = mkIte sym c x y

  floatIsNaN sym (FloatExpr _ x _) =
    pure . backendPred sym $! BF.bfIsNaN x
  floatIsNaN sym x = floatIEEELogicUnOp FloatIsNaN sym x

  floatIsInf sym (FloatExpr _ x _) =
    pure . backendPred sym $! BF.bfIsInf x
  floatIsInf sym x = floatIEEELogicUnOp FloatIsInf sym x

  floatIsZero sym (FloatExpr _ x _) =
    pure . backendPred sym $! BF.bfIsZero x
  floatIsZero sym x = floatIEEELogicUnOp FloatIsZero sym x

  floatIsPos sym (FloatExpr _ x _) =
    pure . backendPred sym $! BF.bfIsPos x
  floatIsPos sym x = floatIEEELogicUnOp FloatIsPos sym x

  floatIsNeg sym (FloatExpr _ x _) =
    pure . backendPred sym $! BF.bfIsNeg x
  floatIsNeg sym x = floatIEEELogicUnOp FloatIsNeg sym x

  floatIsSubnorm sym (FloatExpr fpp x _) =
    pure . backendPred sym $! BF.bfIsSubnormal (fppOpts fpp RNE) x
  floatIsSubnorm sym x = floatIEEELogicUnOp FloatIsSubnorm sym x

  floatIsNorm sym (FloatExpr fpp x _) =
    pure . backendPred sym $! BF.bfIsNormal (fppOpts fpp RNE) x
  floatIsNorm sym x = floatIEEELogicUnOp FloatIsNorm sym x

  floatCast sym fpp r (FloatExpr _ x _) =
    floatLit sym fpp (bfStatus (BF.bfRoundFloat (fppOpts fpp r) x))
  floatCast sym fpp r x
    | FloatingPointPrecisionRepr eb sb <- fpp
    , Just (FloatCast (FloatingPointPrecisionRepr eb' sb') _ fval) <- asApp x
    , natValue eb <= natValue eb'
    , natValue sb <= natValue sb'
    , Just Refl <- testEquality (BaseFloatRepr fpp) (exprType fval)
    = return fval
    | otherwise = sbMakeExpr sym $ FloatCast fpp r x

  floatRound sym r (FloatExpr fpp x _) =
    floatLit sym fpp (floatRoundToInt fpp r x)
  floatRound sym r x = floatIEEEArithUnOpR FloatRound sym r x

  floatFromBinary sym fpp x
    | Just bv <- asBV x
    = floatLit sym fpp (BF.bfFromBits (fppOpts fpp RNE) (BV.asUnsigned bv))
    | Just (FloatToBinary fpp' fval) <- asApp x
    , Just Refl <- testEquality fpp fpp'
    = return fval
    | otherwise = sbMakeExpr sym $ FloatFromBinary fpp x

  floatToBinary sym (FloatExpr fpp@(FloatingPointPrecisionRepr eb sb) x _)
    | Just LeqProof <- isPosNat (addNat eb sb) =
        bvLit sym (addNat eb sb) (BV.mkBV (addNat eb sb) (BF.bfToBits (fppOpts fpp RNE) x))
  floatToBinary sym x = case exprType x of
    BaseFloatRepr fpp | LeqProof <- lemmaFloatPrecisionIsPos fpp ->
      sbMakeExpr sym $ FloatToBinary fpp x

  floatMin sym x y =
    iteList floatIte sym
      [ (floatIsNaN sym x, pure y)
      , (floatIsNaN sym y, pure x)
      , (floatLt sym x y , pure x)
      , (floatLt sym y x , pure y)
      , (floatEq sym x y , pure x) -- NB logical equality, not IEEE 754 equality
      ]
      -- The only way to get here is if x and y are zeros
      -- with different sign.
      -- Return one of the two values nondeterministicly.
      (do b <- freshConstant sym emptySymbol BaseBoolRepr
          floatIte sym b x y)

  floatMax sym x y =
    iteList floatIte sym
      [ (floatIsNaN sym x, pure y)
      , (floatIsNaN sym y, pure x)
      , (floatLt sym x y , pure y)
      , (floatLt sym y x , pure x)
      , (floatEq sym x y , pure x) -- NB logical equality, not IEEE 754 equality
      ]
      -- The only way to get here is if x and y are zeros
      -- with different sign.
      -- Return one of the two values nondeterministicly.
      (do b <- freshConstant sym emptySymbol BaseBoolRepr
          floatIte sym b x y)

  bvToFloat sym fpp r x
    | Just bv <- asBV x = floatLit sym fpp (floatFromInteger (fppOpts fpp r) (BV.asUnsigned bv))
    | otherwise = sbMakeExpr sym (BVToFloat fpp r x)

  sbvToFloat sym fpp r x
    | Just bv <- asBV x = floatLit sym fpp (floatFromInteger (fppOpts fpp r) (BV.asSigned (bvWidth x) bv))
    | otherwise = sbMakeExpr sym (SBVToFloat fpp r x)

  realToFloat sym fpp r x
    | Just x' <- asRational x = floatLit sym fpp (floatFromRational (fppOpts fpp r) x')
    | otherwise = sbMakeExpr sym (RealToFloat fpp r x)

  floatToBV sym w r x
    | FloatExpr _ bf _ <- x
    , Just i <- floatToInteger r bf
    , 0 <= i && i <= maxUnsigned w
    = bvLit sym w (BV.mkBV w i)

    | otherwise = sbMakeExpr sym (FloatToBV w r x)

  floatToSBV sym w r x
    | FloatExpr _ bf _ <- x
    , Just i <- floatToInteger r bf
    , minSigned w <= i && i <= maxSigned w
    = bvLit sym w (BV.mkBV w i)

    | otherwise = sbMakeExpr sym (FloatToSBV w r x)

  floatToReal sym x
    | FloatExpr _ bf _ <- x
    , Just q <- floatToRational bf
    = realLit sym q

    | otherwise = sbMakeExpr sym (FloatToReal x)

  floatSpecialFunction sym fpp fn args =
    sbMakeExpr sym (FloatSpecialFunction fpp fn (SFn.SpecialFnArgs args))

  ----------------------------------------------------------------------
  -- Cplx operations

  mkComplex sym c = sbMakeExpr sym (Cplx c)

  getRealPart _ e
    | Just (Cplx (r :+ _)) <- asApp e = return r
  getRealPart sym x =
    sbMakeExpr sym (RealPart x)

  getImagPart _ e
    | Just (Cplx (_ :+ i)) <- asApp e = return i
  getImagPart sym x =
    sbMakeExpr sym (ImagPart x)

  cplxGetParts _ e
    | Just (Cplx c) <- asApp e = return c
  cplxGetParts sym x =
    (:+) <$> sbMakeExpr sym (RealPart x)
         <*> sbMakeExpr sym (ImagPart x)



inSameBVSemiRing :: Expr t (BaseBVType w) -> Expr t (BaseBVType w) -> Maybe (Some SR.BVFlavorRepr)
inSameBVSemiRing x y
  | Just (SemiRingSum s1) <- asApp x
  , Just (SemiRingSum s2) <- asApp y
  , SR.SemiRingBVRepr flv1 _w <- WSum.sumRepr s1
  , SR.SemiRingBVRepr flv2 _w <- WSum.sumRepr s2
  , Just Refl <- testEquality flv1 flv2
  = Just (Some flv1)

  | otherwise
  = Nothing

floatIEEEArithBinOp
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> e (BaseFloatType fpp)
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithBinOp ctor sym x y =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp x y
floatIEEEArithBinOpR
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> RoundingMode
     -> e (BaseFloatType fpp)
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithBinOpR ctor sym r x y =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp r x y
floatIEEEArithUnOp
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithUnOp ctor sym x =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp x
floatIEEEArithUnOpR
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> RoundingMode
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithUnOpR ctor sym r x =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp r x


floatIEEELogicBinOp
  :: (e ~ Expr t)
  => (e (BaseFloatType fpp) -> e (BaseFloatType fpp) -> App e BaseBoolType)
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e BaseBoolType)
floatIEEELogicBinOp ctor sym x y = sbMakeExpr sym $ ctor x y
floatIEEELogicUnOp
  :: (e ~ Expr t)
  => (e (BaseFloatType fpp) -> App e BaseBoolType)
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> IO (e BaseBoolType)
floatIEEELogicUnOp ctor sym x = sbMakeExpr sym $ ctor x


----------------------------------------------------------------------
-- Float interpretations

type instance SymInterpretedFloatType (ExprBuilder t st (Flags FloatReal)) fi =
  BaseRealType

instance IsInterpretedFloatExprBuilder (ExprBuilder t st (Flags FloatReal)) where
  iFloatPZero sym _ = return $ realZero sym
  iFloatNZero sym _ = return $ realZero sym
  iFloatNaN _ _ = fail "NaN cannot be represented as a real value."
  iFloatPInf _ _ = fail "+Infinity cannot be represented as a real value."
  iFloatNInf _ _ = fail "-Infinity cannot be represented as a real value."
  iFloatLitRational sym _ = realLit sym
  iFloatLitSingle sym = realLit sym . toRational
  iFloatLitDouble sym = realLit sym . toRational
  iFloatLitLongDouble sym x =
     case fp80ToRational x of
       Nothing -> fail ("80-bit floating point value does not represent a rational number: " ++ show x)
       Just r  -> realLit sym r
  iFloatNeg = realNeg
  iFloatAbs = realAbs
  iFloatSqrt sym _ = realSqrt sym
  iFloatAdd sym _ = realAdd sym
  iFloatSub sym _ = realSub sym
  iFloatMul sym _ = realMul sym
  iFloatDiv sym _ = realDiv sym
  iFloatRem = realMod
  iFloatMin sym x y = do
    c <- realLe sym x y
    realIte sym c x y
  iFloatMax sym x y = do
    c <- realGe sym x y
    realIte sym c x y
  iFloatFMA sym _ x y z = do
    tmp <- (realMul sym x y)
    realAdd sym tmp z
  iFloatEq = realEq
  iFloatNe = realNe
  iFloatFpEq = realEq
  iFloatFpApart = realNe
  iFloatLe = realLe
  iFloatLt = realLt
  iFloatGe = realGe
  iFloatGt = realGt
  iFloatIte = realIte
  iFloatIsNaN sym _ = return $ falsePred sym
  iFloatIsInf sym _ = return $ falsePred sym
  iFloatIsZero sym = realEq sym $ realZero sym
  iFloatIsPos sym = realLt sym $ realZero sym
  iFloatIsNeg sym = realGt sym $ realZero sym
  iFloatIsSubnorm sym _ = return $ falsePred sym
  iFloatIsNorm sym = realNe sym $ realZero sym
  iFloatCast _ _ _ = return
  iFloatRound sym r x =
    integerToReal sym =<< case r of
      RNA -> realRound sym x
      RTP -> realCeil sym x
      RTN -> realFloor sym x
      RTZ -> do
        is_pos <- realLt sym (realZero sym) x
        iteM intIte sym is_pos (realFloor sym x) (realCeil sym x)
      RNE -> fail "Unsupported rond to nearest even for real values."
  iFloatFromBinary sym _ x
    | Just (FnApp fn args) <- asNonceApp x
    , "uninterpreted_real_to_float_binary" == solverSymbolAsText (symFnName fn)
    , UninterpFnInfo param_types (BaseBVRepr _) <- symFnInfo fn
    , (Ctx.Empty Ctx.:> BaseRealRepr) <- param_types
    , (Ctx.Empty Ctx.:> rval) <- args
    = return rval
    | otherwise = mkFreshUninterpFnApp sym
                                       "uninterpreted_real_from_float_binary"
                                       (Ctx.Empty Ctx.:> x)
                                       knownRepr
  iFloatToBinary sym fi x =
    mkFreshUninterpFnApp sym
                         "uninterpreted_real_to_float_binary"
                         (Ctx.Empty Ctx.:> x)
                         (floatInfoToBVTypeRepr fi)
  iBVToFloat sym _ _ = uintToReal sym
  iSBVToFloat sym _ _ = sbvToReal sym
  iRealToFloat _ _ _ = return
  iFloatToBV sym w _ x = realToBV sym x w
  iFloatToSBV sym w _ x = realToSBV sym x w
  iFloatToReal _ = return
  iFloatSpecialFunction sym _ fn args = realSpecialFunction sym fn args
  iFloatBaseTypeRepr _ _ = knownRepr

type instance SymInterpretedFloatType (ExprBuilder t st (Flags FloatUninterpreted)) fi =
  BaseBVType (FloatInfoToBitWidth fi)

instance IsInterpretedFloatExprBuilder (ExprBuilder t st (Flags FloatUninterpreted)) where
  iFloatPZero sym =
    floatUninterpArithCt "uninterpreted_float_pzero" sym . iFloatBaseTypeRepr sym
  iFloatNZero sym =
    floatUninterpArithCt "uninterpreted_float_nzero" sym . iFloatBaseTypeRepr sym
  iFloatNaN sym =
    floatUninterpArithCt "uninterpreted_float_nan" sym . iFloatBaseTypeRepr sym
  iFloatPInf sym =
    floatUninterpArithCt "uninterpreted_float_pinf" sym . iFloatBaseTypeRepr sym
  iFloatNInf sym =
    floatUninterpArithCt "uninterpreted_float_ninf" sym . iFloatBaseTypeRepr sym
  iFloatLitRational sym fi x = iRealToFloat sym fi RNE =<< realLit sym x
  iFloatLitSingle sym x =
    iFloatFromBinary sym SingleFloatRepr
      =<< (bvLit sym knownNat $ BV.word32 $ castFloatToWord32 x)
  iFloatLitDouble sym x =
    iFloatFromBinary sym DoubleFloatRepr
      =<< (bvLit sym knownNat $ BV.word64 $ castDoubleToWord64 x)
  iFloatLitLongDouble sym x =
    iFloatFromBinary sym X86_80FloatRepr
      =<< (bvLit sym knownNat $ BV.mkBV knownNat $ fp80ToBits x)

  iFloatNeg = floatUninterpArithUnOp "uninterpreted_float_neg"
  iFloatAbs = floatUninterpArithUnOp "uninterpreted_float_abs"
  iFloatSqrt = floatUninterpArithUnOpR "uninterpreted_float_sqrt"
  iFloatAdd = floatUninterpArithBinOpR "uninterpreted_float_add"
  iFloatSub = floatUninterpArithBinOpR "uninterpreted_float_sub"
  iFloatMul = floatUninterpArithBinOpR "uninterpreted_float_mul"
  iFloatDiv = floatUninterpArithBinOpR "uninterpreted_float_div"
  iFloatRem = floatUninterpArithBinOp "uninterpreted_float_rem"
  iFloatMin = floatUninterpArithBinOp "uninterpreted_float_min"
  iFloatMax = floatUninterpArithBinOp "uninterpreted_float_max"
  iFloatFMA sym r x y z = do
    let ret_type = exprType x
    r_arg <- roundingModeToSymInt sym r
    mkUninterpFnApp sym
                    "uninterpreted_float_fma"
                    (Ctx.empty Ctx.:> r_arg Ctx.:> x Ctx.:> y Ctx.:> z)
                    ret_type
  iFloatEq = isEq
  iFloatNe sym x y = notPred sym =<< isEq sym x y
  iFloatFpEq = floatUninterpLogicBinOp "uninterpreted_float_fp_eq"
  iFloatFpApart = floatUninterpLogicBinOp "uninterpreted_float_fp_apart"
  iFloatLe = floatUninterpLogicBinOp "uninterpreted_float_le"
  iFloatLt = floatUninterpLogicBinOp "uninterpreted_float_lt"
  iFloatGe sym x y = floatUninterpLogicBinOp "uninterpreted_float_le" sym y x
  iFloatGt sym x y = floatUninterpLogicBinOp "uninterpreted_float_lt" sym y x
  iFloatIte = baseTypeIte
  iFloatIsNaN = floatUninterpLogicUnOp "uninterpreted_float_is_nan"
  iFloatIsInf = floatUninterpLogicUnOp "uninterpreted_float_is_inf"
  iFloatIsZero = floatUninterpLogicUnOp "uninterpreted_float_is_zero"
  iFloatIsPos = floatUninterpLogicUnOp "uninterpreted_float_is_pos"
  iFloatIsNeg = floatUninterpLogicUnOp "uninterpreted_float_is_neg"
  iFloatIsSubnorm = floatUninterpLogicUnOp "uninterpreted_float_is_subnorm"
  iFloatIsNorm = floatUninterpLogicUnOp "uninterpreted_float_is_norm"
  iFloatCast sym =
    floatUninterpCastOp "uninterpreted_float_cast" sym . iFloatBaseTypeRepr sym
  iFloatRound = floatUninterpArithUnOpR "uninterpreted_float_round"
  iFloatFromBinary _ _ = return
  iFloatToBinary _ _ = return
  iBVToFloat sym =
    floatUninterpCastOp "uninterpreted_bv_to_float" sym . iFloatBaseTypeRepr sym
  iSBVToFloat sym =
    floatUninterpCastOp "uninterpreted_sbv_to_float" sym . iFloatBaseTypeRepr sym
  iRealToFloat sym =
    floatUninterpCastOp "uninterpreted_real_to_float" sym . iFloatBaseTypeRepr sym
  iFloatToBV sym =
    floatUninterpCastOp "uninterpreted_float_to_bv" sym . BaseBVRepr
  iFloatToSBV sym =
    floatUninterpCastOp "uninterpreted_float_to_sbv" sym . BaseBVRepr
  iFloatToReal sym x =
    mkUninterpFnApp sym
                    "uninterpreted_float_to_real"
                    (Ctx.empty Ctx.:> x)
                    knownRepr

  iFloatSpecialFunction sym fi fn args =
    floatUninterpSpecialFn sym (iFloatBaseTypeRepr sym fi) fn args

  iFloatBaseTypeRepr _ = floatInfoToBVTypeRepr

floatUninterpArithBinOp
  :: (e ~ Expr t) => String -> ExprBuilder t st fs -> e bt -> e bt -> IO (e bt)
floatUninterpArithBinOp fn sym x y =
  let ret_type = exprType x
  in  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x Ctx.:> y) ret_type

floatUninterpSpecialFn
  :: (e ~ Expr t)
  => ExprBuilder t sf tfs
  -> BaseTypeRepr bt
  -> SFn.SpecialFunction args
  -> Assignment (SFn.SpecialFnArg e bt) args
  -> IO (e bt)
floatUninterpSpecialFn sym btr fn Ctx.Empty =
  do fn_name <- unsafeUserSymbol ("uninterpreted_" ++ show fn)
     fn' <- cachedUninterpFn sym fn_name Ctx.Empty btr freshTotalUninterpFn
     applySymFn sym fn' Ctx.Empty

floatUninterpSpecialFn sym btr fn (Ctx.Empty Ctx.:> SFn.SpecialFnArg x) =
  do fn_name <- unsafeUserSymbol ("uninterpreted_" ++ show fn)
     fn' <- cachedUninterpFn sym fn_name (Ctx.Empty Ctx.:> btr) btr freshTotalUninterpFn
     applySymFn sym fn' (Ctx.Empty Ctx.:> x)

floatUninterpSpecialFn sym btr fn (Ctx.Empty Ctx.:> SFn.SpecialFnArg x Ctx.:> SFn.SpecialFnArg y) =
  do fn_name <- unsafeUserSymbol ("uninterpreted_" ++ show fn)
     fn' <- cachedUninterpFn sym fn_name (Ctx.Empty Ctx.:> btr Ctx.:> btr) btr freshTotalUninterpFn
     applySymFn sym fn' (Ctx.Empty Ctx.:> x Ctx.:> y)

floatUninterpSpecialFn _sym _btr fn _args =
  fail $ unwords ["Special function with unexpected arity", show fn]

floatUninterpArithBinOpR
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e bt
  -> e bt
  -> IO (e bt)
floatUninterpArithBinOpR fn sym r x y = do
  let ret_type = exprType x
  r_arg <- roundingModeToSymInt sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x Ctx.:> y) ret_type

floatUninterpArithUnOp
  :: (e ~ Expr t) => String -> ExprBuilder t st fs -> e bt -> IO (e bt)
floatUninterpArithUnOp fn sym x =
  let ret_type = exprType x
  in  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x) ret_type
floatUninterpArithUnOpR
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e bt
  -> IO (e bt)
floatUninterpArithUnOpR fn sym r x = do
  let ret_type = exprType x
  r_arg <- roundingModeToSymInt sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x) ret_type

floatUninterpArithCt
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> BaseTypeRepr bt
  -> IO (e bt)
floatUninterpArithCt fn sym ret_type =
  mkUninterpFnApp sym fn Ctx.empty ret_type

floatUninterpLogicBinOp
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> e bt
  -> e bt
  -> IO (e BaseBoolType)
floatUninterpLogicBinOp fn sym x y =
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x Ctx.:> y) knownRepr

floatUninterpLogicUnOp
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> e bt
  -> IO (e BaseBoolType)
floatUninterpLogicUnOp fn sym x =
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x) knownRepr

floatUninterpCastOp
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> BaseTypeRepr bt
  -> RoundingMode
  -> e bt'
  -> IO (e bt)
floatUninterpCastOp fn sym ret_type r x = do
  r_arg <- roundingModeToSymInt sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x) ret_type

roundingModeToSymInt
  :: (sym ~ ExprBuilder t st fs) => sym -> RoundingMode -> IO (SymInteger sym)
roundingModeToSymInt sym = intLit sym . toInteger . fromEnum


type instance SymInterpretedFloatType (ExprBuilder t st (Flags FloatIEEE)) fi =
  BaseFloatType (FloatInfoToPrecision fi)

instance IsInterpretedFloatExprBuilder (ExprBuilder t st (Flags FloatIEEE)) where
  iFloatPZero sym = floatPZero sym . floatInfoToPrecisionRepr
  iFloatNZero sym = floatNZero sym . floatInfoToPrecisionRepr
  iFloatNaN sym = floatNaN sym . floatInfoToPrecisionRepr
  iFloatPInf sym = floatPInf sym . floatInfoToPrecisionRepr
  iFloatNInf sym = floatNInf sym . floatInfoToPrecisionRepr
  iFloatLitRational sym = floatLitRational sym . floatInfoToPrecisionRepr
  iFloatLitSingle sym x =
    floatFromBinary sym knownRepr
      =<< (bvLit sym knownNat $ BV.word32 $ castFloatToWord32 x)
  iFloatLitDouble sym x =
    floatFromBinary sym knownRepr
      =<< (bvLit sym knownNat $ BV.word64 $ castDoubleToWord64 x)
  iFloatLitLongDouble sym (X86_80Val e s) = do
    el <- bvLit sym (knownNat @16) $ BV.word16 e
    sl <- bvLit sym (knownNat @64) $ BV.word64 s
    fl <- bvConcat sym el sl
    floatFromBinary sym knownRepr fl
    -- n.b. This may not be valid semantically for operations
    -- performed on 80-bit values, but it allows them to be present in
    -- formulas.
  iFloatNeg = floatNeg
  iFloatAbs = floatAbs
  iFloatSqrt = floatSqrt
  iFloatAdd = floatAdd
  iFloatSub = floatSub
  iFloatMul = floatMul
  iFloatDiv = floatDiv
  iFloatRem = floatRem
  iFloatMin = floatMin
  iFloatMax = floatMax
  iFloatFMA = floatFMA
  iFloatEq = floatEq
  iFloatNe = floatNe
  iFloatFpEq = floatFpEq
  iFloatFpApart = floatFpApart
  iFloatLe = floatLe
  iFloatLt = floatLt
  iFloatGe = floatGe
  iFloatGt = floatGt
  iFloatIte = floatIte
  iFloatIsNaN = floatIsNaN
  iFloatIsInf = floatIsInf
  iFloatIsZero = floatIsZero
  iFloatIsPos = floatIsPos
  iFloatIsNeg = floatIsNeg
  iFloatIsSubnorm = floatIsSubnorm
  iFloatIsNorm = floatIsNorm
  iFloatCast sym = floatCast sym . floatInfoToPrecisionRepr
  iFloatRound = floatRound
  iFloatFromBinary sym fi x = case fi of
    HalfFloatRepr         -> floatFromBinary sym knownRepr x
    SingleFloatRepr       -> floatFromBinary sym knownRepr x
    DoubleFloatRepr       -> floatFromBinary sym knownRepr x
    QuadFloatRepr         -> floatFromBinary sym knownRepr x
    X86_80FloatRepr       -> fail "x86_80 is not an IEEE-754 format."
    DoubleDoubleFloatRepr -> fail "double-double is not an IEEE-754 format."
  iFloatToBinary sym fi x = case fi of
    HalfFloatRepr         -> floatToBinary sym x
    SingleFloatRepr       -> floatToBinary sym x
    DoubleFloatRepr       -> floatToBinary sym x
    QuadFloatRepr         -> floatToBinary sym x
    X86_80FloatRepr       -> fail "x86_80 is not an IEEE-754 format."
    DoubleDoubleFloatRepr -> fail "double-double is not an IEEE-754 format."
  iBVToFloat sym = bvToFloat sym . floatInfoToPrecisionRepr
  iSBVToFloat sym = sbvToFloat sym . floatInfoToPrecisionRepr
  iRealToFloat sym = realToFloat sym . floatInfoToPrecisionRepr
  iFloatToBV = floatToBV
  iFloatToSBV = floatToSBV
  iFloatToReal = floatToReal
  iFloatSpecialFunction sym fi fn args =
    floatSpecialFunction sym (floatInfoToPrecisionRepr fi) fn args
  iFloatBaseTypeRepr _ = BaseFloatRepr . floatInfoToPrecisionRepr


instance IsSymExprBuilder (ExprBuilder t st fs) where
  freshConstant sym nm tp = do
    v <- sbMakeBoundVar sym nm tp UninterpVarKind Nothing
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarExpr v

  freshBoundedBV sym nm w Nothing Nothing = freshConstant sym nm (BaseBVRepr w)
  freshBoundedBV sym nm w mlo mhi =
    do unless boundsOK (Ex.throwIO (InvalidRange (BaseBVRepr w) (fmap toInteger mlo) (fmap toInteger mhi)))
       v <- sbMakeBoundVar sym nm (BaseBVRepr w) UninterpVarKind (Just $! (BVD.range w lo hi))
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   boundsOK = lo <= hi && minUnsigned w <= lo && hi <= maxUnsigned w
   lo = maybe (minUnsigned w) toInteger mlo
   hi = maybe (maxUnsigned w) toInteger mhi

  freshBoundedSBV sym nm w Nothing Nothing = freshConstant sym nm (BaseBVRepr w)
  freshBoundedSBV sym nm w mlo mhi =
    do unless boundsOK (Ex.throwIO (InvalidRange (BaseBVRepr w) mlo mhi))
       v <- sbMakeBoundVar sym nm (BaseBVRepr w) UninterpVarKind (Just $! (BVD.range w lo hi))
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   boundsOK = lo <= hi && minSigned w <= lo && hi <= maxSigned w
   lo = fromMaybe (minSigned w) mlo
   hi = fromMaybe (maxSigned w) mhi

  freshBoundedInt sym nm mlo mhi =
    do unless (boundsOK mlo mhi) (Ex.throwIO (InvalidRange BaseIntegerRepr mlo mhi))
       v <- sbMakeBoundVar sym nm BaseIntegerRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   boundsOK (Just lo) (Just hi) = lo <= hi
   boundsOK _ _ = True

   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! MultiRange (Inclusive lo) Unbounded
   absVal Nothing (Just hi) = Just $! MultiRange Unbounded (Inclusive hi)
   absVal (Just lo) (Just hi) = Just $! MultiRange (Inclusive lo) (Inclusive hi)

  freshBoundedReal sym nm mlo mhi =
    do unless (boundsOK mlo mhi) (Ex.throwIO (InvalidRange BaseRealRepr mlo mhi))
       v <- sbMakeBoundVar sym nm BaseRealRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   boundsOK (Just lo) (Just hi) = lo <= hi
   boundsOK _ _ = True

   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! RAV (MultiRange (Inclusive lo) Unbounded) Nothing
   absVal Nothing (Just hi) = Just $! RAV (MultiRange Unbounded (Inclusive hi)) Nothing
   absVal (Just lo) (Just hi) = Just $! RAV (MultiRange (Inclusive lo) (Inclusive hi)) Nothing

  freshLatch sym nm tp = do
    v <- sbMakeBoundVar sym nm tp LatchVarKind Nothing
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarExpr v

  exprUninterpConstants _sym expr =
    (runST $ VI.collectVarInfo $ VI.recordExprVars VI.ExistsOnly expr) ^. VI.uninterpConstants

  freshBoundVar sym nm tp =
    sbMakeBoundVar sym nm tp QuantifierVarKind Nothing

  varExpr _ = BoundVarExpr

  forallPred sym bv e = sbNonceExpr sym $ Forall bv e

  existsPred sym bv e = sbNonceExpr sym $ Exists bv e

  ----------------------------------------------------------------------
  -- SymFn operations.

  -- | Create a function defined in terms of previous functions.
  definedFn sym fn_name bound_vars result policy = do
    l <- curProgramLoc sym
    n <- sbFreshSymFnNonce sym
    let fn = ExprSymFn { symFnId   = n
                         , symFnName = fn_name
                         , symFnInfo = DefinedFnInfo bound_vars result policy
                         , symFnLoc  = l
                         }
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  freshTotalUninterpFn sym fn_name arg_types ret_type = do
    n <- sbFreshSymFnNonce sym
    l <- curProgramLoc sym
    let fn = ExprSymFn { symFnId = n
                         , symFnName = fn_name
                         , symFnInfo = UninterpFnInfo arg_types ret_type
                         , symFnLoc = l
                         }
    seq fn $ do
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  applySymFn sym fn args = do
   case symFnInfo fn of
     DefinedFnInfo bound_vars e policy
       | shouldUnfold policy args ->
           evalBoundVars sym e bound_vars args
     MatlabSolverFnInfo f _ _ -> do
       evalMatlabSolverFn f sym args
     _ -> sbNonceExpr sym $! FnApp fn args

  substituteBoundVars sym subst e = do
    tbls <- stToIO $ do
      expr_tbl <- PH.newSized $ PM.size subst
      fn_tbl <- PH.new
      PM.traverseWithKey_ (PH.insert expr_tbl . BoundVarExpr) subst
      return $ EvalHashTables
        { exprTable = expr_tbl
        , fnTable  = fn_tbl
        }
    evalBoundVars' tbls sym e

  substituteSymFns sym subst e = do
    tbls <- stToIO $ do
      expr_tbl <- PH.new
      fn_tbl <- PH.newSized $ PM.size subst
      PM.traverseWithKey_
        (\(SymFnWrapper f) (SymFnWrapper g) -> PH.insert fn_tbl (symFnId f) (CachedSymFn True g))
        subst
      return $ EvalHashTables
        { exprTable = expr_tbl
        , fnTable  = fn_tbl
        }
    evalBoundVars' tbls sym e

  transformPredBV2LIA sym exprs = do
    expr_tbl <- stToIO PH.new
    fn_tbl  <- stToIO PH.new
    let tbls = EvalHashTables
          { exprTable = expr_tbl
          , fnTable  = fn_tbl
          }
    subst <- H.new
    fn_subst <- H.new
    let transformer_tbls = ExprTransformerTables
          { evalTables = tbls
          , transformerSubst = subst
          , transformerFnSubst = fn_subst
          }
    let ?transformCmpTp1ToTp2 = transformCmpBV2LIA
        ?transformExprTp1ToTp2 = transformExprBV2LIA
    lia_exprs <- either fail return =<<
      runExprTransformer (mapM (transformPred sym) exprs) transformer_tbls
    bv_to_lia_fn_subst <- Map.fromList <$>
      map (\(SomeExprSymFn f, SomeExprSymFn g) -> (SomeSymFn f, SomeSymFn g)) <$>
      H.toList fn_subst
    return (lia_exprs, bv_to_lia_fn_subst)

  transformSymFnLIA2BV sym (SomeSymFn fn) = do
    expr_tbl <- stToIO PH.new
    fn_tbl  <- stToIO PH.new
    let tbls = EvalHashTables
          { exprTable = expr_tbl
          , fnTable  = fn_tbl
          }
    subst <- H.new
    fn_subst <- H.new
    let transformer_tbls = ExprTransformerTables
          { evalTables = tbls
          , transformerSubst = subst
          , transformerFnSubst = fn_subst
          }
    let ?transformCmpTp1ToTp2 = transformCmpLIA2BV
        ?transformExprTp1ToTp2 = transformExprLIA2BV
    either fail (\(SomeExprSymFn fn') -> return $ SomeSymFn fn') =<<
      runExprTransformer (transformFn sym $ SomeExprSymFn fn) transformer_tbls


instance IsInterpretedFloatExprBuilder (ExprBuilder t st fs) => IsInterpretedFloatSymExprBuilder (ExprBuilder t st fs)


--------------------------------------------------------------------------------
-- MatlabSymbolicArrayBuilder instance

instance MatlabSymbolicArrayBuilder (ExprBuilder t st fs) where
  mkMatlabSolverFn sym fn_id = do
    let key = MatlabFnWrapper fn_id
    mr <- stToIO $ PH.lookup (sbMatlabFnCache sym) key
    case mr of
      Just (ExprSymFnWrapper f) -> return f
      Nothing -> do
        let tps = matlabSolverArgTypes fn_id
        vars <- traverseFC (freshBoundVar sym emptySymbol) tps
        r <- evalMatlabSolverFn fn_id sym (fmapFC BoundVarExpr vars)
        l <- curProgramLoc sym
        n <- sbFreshSymFnNonce sym
        let f = ExprSymFn { symFnId   = n
                            , symFnName = emptySymbol
                            , symFnInfo = MatlabSolverFnInfo fn_id vars r
                            , symFnLoc  = l
                            }
        updateVarBinding sym emptySymbol (FnSymbolBinding f)
        stToIO $ PH.insert (sbMatlabFnCache sym) key (ExprSymFnWrapper f)
        return f

unsafeUserSymbol :: String -> IO SolverSymbol
unsafeUserSymbol s =
  case userSymbol s of
    Left err -> fail (show err)
    Right symbol  -> return symbol

cachedUninterpFn
  :: (sym ~ ExprBuilder t st fs)
  => sym
  -> SolverSymbol
  -> Ctx.Assignment BaseTypeRepr args
  -> BaseTypeRepr ret
  -> (  sym
     -> SolverSymbol
     -> Ctx.Assignment BaseTypeRepr args
     -> BaseTypeRepr ret
     -> IO (SymFn sym args ret)
     )
  -> IO (SymFn sym args ret)
cachedUninterpFn sym fn_name arg_types ret_type handler = do
  fn_cache <- readIORef $ sbUninterpFnCache sym
  case Map.lookup fn_key fn_cache of
    Just (SomeSymFn fn)
      | Just Refl <- testEquality (fnArgTypes fn) arg_types
      , Just Refl <- testEquality (fnReturnType fn) ret_type
      -> return fn
      | otherwise
      -> fail "Duplicate uninterpreted function declaration."
    Nothing -> do
      fn <- handler sym fn_name arg_types ret_type
      atomicModifyIORef' (sbUninterpFnCache sym) (\m -> (Map.insert fn_key (SomeSymFn fn) m, ()))
      return fn
  where fn_key =  (fn_name, Some (arg_types Ctx.:> ret_type))

mkUninterpFnApp
  :: (sym ~ ExprBuilder t st fs)
  => sym
  -> String
  -> Ctx.Assignment (SymExpr sym) args
  -> BaseTypeRepr ret
  -> IO (SymExpr sym ret)
mkUninterpFnApp sym str_fn_name args ret_type = do
  fn_name <- unsafeUserSymbol str_fn_name
  let arg_types = fmapFC exprType args
  fn <- cachedUninterpFn sym fn_name arg_types ret_type freshTotalUninterpFn
  applySymFn sym fn args

mkFreshUninterpFnApp
  :: (sym ~ ExprBuilder t st fs)
  => sym
  -> String
  -> Ctx.Assignment (SymExpr sym) args
  -> BaseTypeRepr ret
  -> IO (SymExpr sym ret)
mkFreshUninterpFnApp sym str_fn_name args ret_type = do
  fn_name <- unsafeUserSymbol str_fn_name
  let arg_types = fmapFC exprType args
  fn <- freshTotalUninterpFn sym fn_name arg_types ret_type
  applySymFn sym fn args
