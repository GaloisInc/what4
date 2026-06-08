{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Working with finite fields of dynamic orders.
module What4.SFF
  ( -- * Interface
    SFF(..)
  , ffBounds
  , ffOrder
  , ffEq
  , ffIte
  , ffLit
  , ffAsLit
  , ffFresh
  , ffAdd
  , ffMul
  , ffSub
  , ffDiv
  , ffNeg
  , ffRecip

    -- * Exceptions
  , FFTypeError(..)
  ) where

import Control.Exception
import Data.Parameterized.Fin (finToNat, mkFinModN)
import Data.Parameterized.NatRepr
import Data.Parameterized.Some (Some(..))
import GHC.TypeNats

import qualified What4.Interface as W
import What4.Interface
  (IsExpr, IsExprBuilder, IsSymExprBuilder, Pred, SymExpr, SymFF)
import What4.Panic (panic)

data SFF sym where
  SFF :: (IsExpr (SymExpr sym), 2 <= p) => SymFF sym p -> SFF sym

instance Show (SFF sym) where
  show (SFF ff) = show $ W.printSymExpr ff

--------------------------------------------------------------------------------

-- | This exception is thrown if the finite field orders don't match.
data FFTypeError =
  FFTypeError { orderExpected :: Some NatRepr
              , orderActual   :: Some NatRepr
              }
    deriving Show

instance Exception FFTypeError

ffTypeError :: NatRepr p1 -> NatRepr p2 -> IO a
ffTypeError p1 p2 =
  throwIO FFTypeError { orderExpected = Some p1
                      , orderActual   = Some p2
                      }

--------------------------------------------------------------------------------

-- | See 'W.ffBounds'.
ffBounds :: SFF sym -> Maybe (Natural, Natural)
ffBounds (SFF x) =
  fmap (\(lo, hi) -> (finToNat lo, finToNat hi)) (W.ffBounds x)

-- | See 'W.ffOrder'.
ffOrder :: SFF sym -> Natural
ffOrder (SFF x) = natValue (W.ffOrder x)

-- | See 'W.ffEq'.
ffEq ::
  IsExprBuilder sym =>
  sym -> SFF sym -> SFF sym -> IO (Pred sym)
ffEq sym (SFF x) (SFF y) =
  let p1 = W.ffOrder x
      p2 = W.ffOrder y
  in
  case testEquality p1 p2 of
    Just Refl -> W.ffEq sym x y
    _         -> ffTypeError p1 p2

-- | See 'W.ffIte'.
ffIte ::
  IsExprBuilder sym =>
  sym -> Pred sym -> SFF sym -> SFF sym -> IO (SFF sym)
ffIte sym p (SFF x) (SFF y) =
  let p1 = W.ffOrder x
      p2 = W.ffOrder y
  in
  case testEquality p1 p2 of
    Just Refl -> SFF <$> W.ffIte sym p x y
    _         -> ffTypeError p1 p2

-- | Create a finite field element with the given order @p@ and value @e@,
-- where @e@ is reduced modulo @n@. (See also 'W.ffLit'.)
--
-- Precondition: @p@ must be prime.
ffLit ::
  IsExprBuilder sym =>
  sym ->
  -- | Order
  Natural ->
  -- | Value
  Natural ->
  IO (SFF sym)
ffLit sym p e
  | Some (pr :: NatRepr p) <- mkNatRepr p
  , Some er <- mkNatRepr e
  = do LeqProof <-
         case testLeq (knownNat @2) pr of
           Just pf -> pure pf
           Nothing -> panic "ffLit" ["modulus is < 2", show p]
       LeqProof <- pure $ leqSub (LeqProof @2 @p) (LeqProof @1 @2)
       SFF <$> W.ffLit sym pr (mkFinModN pr er)

-- | See 'asFF'.
ffAsLit :: SFF sym -> Maybe Natural
ffAsLit (SFF x) = finToNat <$> W.asFF x

-- | See 'W.freshConstant'.
ffFresh ::
  IsSymExprBuilder sym => sym -> W.SolverSymbol -> Natural -> IO (SFF sym)
ffFresh sym nm p
  | Some pr <- mkNatRepr p
  = do LeqProof <-
         case testLeq (knownNat @2) pr of
           Just pf -> pure pf
           Nothing -> panic "ffFresh" ["modulus is < 2", show p]
       SFF <$> W.freshConstant sym nm (W.BaseFFRepr pr)

-- | See 'W.ffAdd'.
ffAdd :: IsExprBuilder sym => sym -> SFF sym -> SFF sym -> IO (SFF sym)
ffAdd sym (SFF x) (SFF y) =
  let p1 = W.ffOrder x
      p2 = W.ffOrder y
  in
  case testEquality p1 p2 of
    Just Refl -> SFF <$> W.ffAdd sym x y
    _         -> ffTypeError p1 p2

-- | See 'W.ffMul'.
ffMul :: IsExprBuilder sym => sym -> SFF sym -> SFF sym -> IO (SFF sym)
ffMul sym (SFF x) (SFF y) =
  let p1 = W.ffOrder x
      p2 = W.ffOrder y
  in
  case testEquality p1 p2 of
    Just Refl -> SFF <$> W.ffMul sym x y
    _         -> ffTypeError p1 p2

-- | See 'W.ffAdd'.
ffSub :: IsExprBuilder sym => sym -> SFF sym -> SFF sym -> IO (SFF sym)
ffSub sym (SFF x) (SFF y) =
  let p1 = W.ffOrder x
      p2 = W.ffOrder y
  in
  case testEquality p1 p2 of
    Just Refl -> SFF <$> W.ffSub sym x y
    _         -> ffTypeError p1 p2

-- | See 'W.ffDiv'.
ffDiv :: IsExprBuilder sym => sym -> SFF sym -> SFF sym -> IO (SFF sym)
ffDiv sym (SFF x) (SFF y) =
  let p1 = W.ffOrder x
      p2 = W.ffOrder y
  in
  case testEquality p1 p2 of
    Just Refl -> SFF <$> W.ffDiv sym x y
    _         -> ffTypeError p1 p2

-- | See 'W.ffNeg'.
ffNeg :: IsExprBuilder sym => sym -> SFF sym -> IO (SFF sym)
ffNeg sym (SFF x) = SFF <$> W.ffNeg sym x

-- | See 'W.ffRecip'.
ffRecip :: IsExprBuilder sym => sym -> SFF sym -> IO (SFF sym)
ffRecip sym (SFF x) = SFF <$> W.ffRecip sym x
