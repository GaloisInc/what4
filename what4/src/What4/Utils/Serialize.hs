{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
module What4.Utils.Serialize
    (
      withRounding
    , makeSymbol
    , asyncLinked
    , withAsyncLinked
    ) where

import qualified Control.Exception as E
import           Text.Printf ( printf )
import qualified Data.BitVector.Sized as BV
import           What4.BaseTypes
import qualified What4.Interface as S
import           What4.Symbol ( SolverSymbol, userSymbol )


import qualified UnliftIO as U

----------------------------------------------------------------
-- * Async

-- | Fork an async action that is linked to the parent thread, but can
-- be safely 'U.cancel'd without also killing the parent thread.
--
-- Note that if your async doesn't return unit, then you probably want
-- to 'U.wait' for it instead, which eliminates the need for linking
-- it. Also, if you plan to cancel the async near where you fork it,
-- then 'withAsyncLinked' is a better choice than using this function
-- and subsequently canceling, since it ensures cancellation.
--
-- See https://github.com/simonmar/async/issues/25 for a perhaps more
-- robust, but also harder to use version of this. The linked version
-- is harder to use because it requires a special version of @cancel@.
asyncLinked :: (U.MonadUnliftIO m) => m () -> m (U.Async ())
asyncLinked action = do
  -- We use 'U.mask' to avoid a race condition between starting the
  -- async and running @action@. Without 'U.mask' here, an async
  -- exception (e.g. via 'U.cancel') could arrive after
  -- @handleUnliftIO@ starts to run but before @action@ starts.
  U.mask $ \restore -> do
  a <- U.async $ handleUnliftIO threadKilledHandler (restore action)
  restore $ do
  U.link a
  return a

-- | Handle asynchronous 'E.ThreadKilled' exceptions without killing the parent
-- thread. All other forms of asynchronous exceptions are rethrown.
threadKilledHandler :: Monad m => E.AsyncException -> m ()
threadKilledHandler E.ThreadKilled = return ()
threadKilledHandler e              = E.throw e

-- | A version of 'U.withAsync' that safely links the child. See
-- 'asyncLinked'.
withAsyncLinked :: (U.MonadUnliftIO m) => m () -> (U.Async () -> m a) -> m a
withAsyncLinked child parent = do
  U.mask $ \restore -> do
  U.withAsync (handleUnliftIO threadKilledHandler $ restore child) $ \a -> restore $ do
  U.link a
  parent a

-- A 'U.MonadUnliftIO' version of 'Control.Exception.handle'.
--
-- The 'U.handle' doesn't catch async exceptions, because the
-- @unliftio@ library uses the @safe-execeptions@ library, not
-- @base@, for it exception handling primitives. This is very
-- confusing if you're not expecting it!
handleUnliftIO :: (U.MonadUnliftIO m, U.Exception e)
               => (e -> m a) -> m a -> m a
handleUnliftIO h a = U.withUnliftIO $ \u ->
  E.handle (U.unliftIO u . h) (U.unliftIO u a)

-- | Try converting any 'String' into a 'SolverSymbol'. If it is an invalid
-- symbol, then error.
makeSymbol :: String -> SolverSymbol
makeSymbol name = case userSymbol sanitizedName of
                    Right symbol -> symbol
                    Left _ -> error $ printf "tried to create symbol with bad name: %s (%s)"
                                             name sanitizedName
  where
    -- We use a custom name sanitizer here because downstream clients may depend
    -- on the format of the name. It would be nice to use 'safeSymbol' here, but
    -- it mangles names with z-encoding in a way that might be unusable
    -- downstream.
    sanitizedName = map (\c -> case c of ' ' -> '_'; '.' -> '_'; _ -> c) name

withRounding
  :: forall sym tp
   . S.IsExprBuilder sym
  => sym
  -> S.SymBV sym 2
  -> (S.RoundingMode -> IO (S.SymExpr sym tp))
  -> IO (S.SymExpr sym tp)
withRounding sym r action = do
  cRNE <- roundingCond S.RNE
  cRTZ <- roundingCond S.RTZ
  cRTP <- roundingCond S.RTP
  S.iteM S.baseTypeIte sym cRNE
    (action S.RNE) $
    S.iteM S.baseTypeIte sym cRTZ
      (action S.RTZ) $
      S.iteM S.baseTypeIte sym cRTP (action S.RTP) (action S.RTN)
 where
  roundingCond :: S.RoundingMode -> IO (S.Pred sym)
  roundingCond rm =
    S.bvEq sym r =<< S.bvLit sym knownNat (BV.mkBV knownNat (roundingModeToBits rm))

roundingModeToBits :: S.RoundingMode -> Integer
roundingModeToBits = \case
  S.RNE -> 0
  S.RTZ -> 1
  S.RTP -> 2
  S.RTN -> 3
  S.RNA -> error $ "unsupported rounding mode: " ++ show S.RNA
