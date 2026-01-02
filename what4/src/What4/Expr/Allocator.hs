{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

{-|
Module      : What4.Expr.Allocator
Description : Expression allocators for controlling hash-consing
Copyright   : (c) Galois Inc, 2015-2022
License     : BSD3
Maintainer  : rdockins@galois.com
-}
module What4.Expr.Allocator
( ExprAllocator(..)
, newStorage
, newCachedStorage

, cacheStartSizeOption
, cacheStartSizeDesc
, cacheTerms
, cacheOptDesc
) where

import           Lens.Micro ( (&) )
import           Control.Monad.ST (stToIO)
import           Data.IORef

import qualified Data.Parameterized.HashTable as PH
import           Data.Parameterized.Nonce

import           What4.BaseTypes
import           What4.Concrete
import           What4.Config as CFG
import           What4.Expr.App
import           What4.ProgramLoc
import           What4.Utils.AbstractDomains

------------------------------------------------------------------------
-- Cache start size

-- | Starting size for element cache when caching is enabled.
--   The default value is 100000 elements.
--
--   This option is named \"backend.cache_start_size\"
cacheStartSizeOption :: ConfigOption BaseIntegerType
cacheStartSizeOption = configOption BaseIntegerRepr "backend.cache_start_size"

-- | The configuration option for setting the size of the initial hash set
--   used by simple builder (measured in number of elements).
cacheStartSizeDesc :: ConfigDesc
cacheStartSizeDesc = mkOpt cacheStartSizeOption sty help (Just (ConcreteInteger 100000))
  where sty = integerWithMinOptSty (CFG.Inclusive 0)
        help = Just "Starting size for element cache"

------------------------------------------------------------------------
-- Cache terms

-- | Indicates if we should cache terms.  When enabled, hash-consing
--   is used to find and deduplicate common subexpressions.
--   Toggling this option from disabled to enabled will allocate a new
--   hash table; toggling it from enabled to disabled will discard
--   the current hash table.  The default value for this option is `False`.
--
--   This option is named \"use_cache\"
cacheTerms :: ConfigOption BaseBoolType
cacheTerms = configOption BaseBoolRepr "use_cache"

cacheOptStyle ::
  NonceGenerator IO t ->
  IORef (ExprAllocator t) ->
  OptionSetting BaseIntegerType ->
  OptionStyle BaseBoolType
cacheOptStyle gen storageRef szSetting =
  boolOptSty & set_opt_onset
        (\mb b -> f (fmap fromConcreteBool mb) (fromConcreteBool b) >> return optOK)
 where
 f :: Maybe Bool -> Bool -> IO ()
 f mb b | mb /= Just b = if b then start else stop
        | otherwise = return ()

 stop  = do s <- newStorage gen
            atomicWriteIORef storageRef s

 start = do sz <- getOpt szSetting
            s <- newCachedStorage gen (fromInteger sz)
            atomicWriteIORef storageRef s

cacheOptDesc ::
  NonceGenerator IO t ->
  IORef (ExprAllocator t) ->
  OptionSetting BaseIntegerType ->
  ConfigDesc
cacheOptDesc gen storageRef szSetting =
  mkOpt
    cacheTerms
    (cacheOptStyle gen storageRef szSetting)
    (Just "Use hash-consing during term construction")
    (Just (ConcreteBool False))


------------------------------------------------------------------------
-- | ExprAllocator provides an interface for creating expressions from
-- an applications.
-- Parameter @t@ is a phantom type brand used to track nonces.
data ExprAllocator t
   = ExprAllocator { appExpr  :: forall tp
                            .  ProgramLoc
                            -> App (Expr t) tp
                            -> AbstractValue tp
                            -> IO (Expr t tp)
                  , nonceExpr :: forall tp
                             .  ProgramLoc
                             -> NonceApp t (Expr t) tp
                             -> AbstractValue tp
                             -> IO (Expr t tp)
                  }


------------------------------------------------------------------------
-- Uncached storage

-- | Create a new storage that does not do hash consing.
newStorage :: NonceGenerator IO t -> IO (ExprAllocator t)
newStorage g = do
  return $! ExprAllocator { appExpr = uncachedExprFn g
                         , nonceExpr = uncachedNonceExpr g
                         }

uncachedExprFn :: NonceGenerator IO t
              -> ProgramLoc
              -> App (Expr t) tp
              -> AbstractValue tp
              -> IO (Expr t tp)
uncachedExprFn g pc a v = do
  n <- freshNonce g
  return $! mkExpr n pc a v

uncachedNonceExpr :: NonceGenerator IO t
                 -> ProgramLoc
                 -> NonceApp t (Expr t) tp
                 -> AbstractValue tp
                 -> IO (Expr t tp)
uncachedNonceExpr g pc p v = do
  n <- freshNonce g
  return $! NonceAppExpr $ NonceAppExprCtor { nonceExprId = n
                                          , nonceExprLoc = pc
                                          , nonceExprApp = p
                                          , nonceExprAbsValue = v
                                          }

------------------------------------------------------------------------
-- Cached storage

cachedNonceExpr :: NonceGenerator IO t
               -> PH.HashTable PH.RealWorld (NonceApp t (Expr t)) (Expr t)
               -> ProgramLoc
               -> NonceApp t (Expr t) tp
               -> AbstractValue tp
               -> IO (Expr t tp)
cachedNonceExpr g h pc p v = do
  me <- stToIO $ PH.lookup h p
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = NonceAppExpr $ NonceAppExprCtor { nonceExprId = n
                                            , nonceExprLoc = pc
                                            , nonceExprApp = p
                                            , nonceExprAbsValue = v
                                            }
      seq e $ stToIO $ PH.insert h p e
      return e


cachedAppExpr :: forall t tp
               . NonceGenerator IO t
              -> PH.HashTable PH.RealWorld (App (Expr t)) (Expr t)
              -> ProgramLoc
              -> App (Expr t) tp
              -> AbstractValue tp
              -> IO (Expr t tp)
cachedAppExpr g h pc a v = do
  me <- stToIO $ PH.lookup h a
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = mkExpr n pc a v
      seq e $ stToIO $ PH.insert h a e
      return e

-- | Create a storage that does hash consing.
newCachedStorage :: forall t
                  . NonceGenerator IO t
                 -> Int
                 -> IO (ExprAllocator t)
newCachedStorage g sz = stToIO $ do
  appCache  <- PH.newSized sz
  predCache <- PH.newSized sz
  return $ ExprAllocator { appExpr = cachedAppExpr g appCache
                        , nonceExpr = cachedNonceExpr g predCache
                        }

