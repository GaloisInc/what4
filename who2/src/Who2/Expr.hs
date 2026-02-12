{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Who2.Expr
  ( Expr(RiskyExpr)
  , mkExpr
  , eId
  , eApp
  , eHash
  , eAbsVal
  , HasBaseType(baseType)
  , maxByHash
  , minByHash
  , pretty
  ) where

import Data.Bits (xor)
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))

import qualified Data.Parameterized.Classes as PC
import Data.Parameterized.Nonce (Nonce, NonceGenerator, freshNonce)
import qualified Prettyprinter as PP

import qualified What4.BaseTypes as BT
import qualified What4.Utils.AbstractDomains as AD

-- | Expression datatype, used as the @f@ parameter to 'Who2.Expr.App'.
data Expr
  (t :: Type)
  (f :: (BT.BaseType -> Type) -> BT.BaseType -> Type)
  (tp :: BT.BaseType)
  = RiskyExpr
    { -- | Unique identifier, used to speed up equality checks
      eId :: {-# UNPACK #-} !(Nonce t tp)
      -- | Precomputed hash of 'eApp', used to speed up equality checks
    , eHash :: {-# UNPACK #-} !Int
      -- | Underlying expression, usually 'Who2.Expr.App'
    , eApp :: !(f (Expr t f) tp)
    , eAbsVal :: !(AD.AbstractValue tp)
    }

-- | Smart constructor that computes the hash of the application.
mkExpr ::
  PC.HashableF (f (Expr t f)) =>
  NonceGenerator IO t ->
  f (Expr t f) tp ->
  AD.AbstractValue tp ->
  IO (Expr t f tp)
mkExpr gen app absVal = do
  nonce <- freshNonce gen
  pure $! RiskyExpr
    { eId = nonce
    , eHash = PC.hashF app
    , eApp = app
    , eAbsVal = absVal
    }
{-# INLINE mkExpr #-}

class HasBaseType f where
  baseType :: f tp -> BT.BaseTypeRepr tp

instance HasBaseType (f (Expr t f)) => HasBaseType (Expr t f) where
  baseType = baseType . eApp

instance
  ( Eq (f (Expr t f) tp)
  , AD.Abstractable tp
  , HasBaseType (f (Expr t f))
  ) => Eq (Expr t f tp) where
  x == y
    | eId x == eId y = True
      -- check for semantic equality before structural
    | Just b <- AD.avCheckEq (baseType x) (eAbsVal x) (eAbsVal y) = b
      -- different hashes => definitely not structurally equal
    | eHash x /= eHash y = False
    | otherwise = eApp x == eApp y

instance AD.HasAbsValue (Expr t f) where
  getAbsValue = eAbsVal
  {-# INLINE getAbsValue #-}

instance
  PC.HashableF (f (Expr t f)) =>
  PC.HashableF (Expr t f) where
  hashWithSaltF salt = (xor salt) . eHash
  hashF = eHash
  {-# INLINE hashF #-}

instance
  ( PC.HashableF (f (Expr t f))
  , Eq (f (Expr t f) tp)
  , AD.Abstractable tp
  , HasBaseType (f (Expr t f))
  ) =>
  PC.Hashable (Expr t f tp) where
  hash = eHash
  hashWithSalt = PC.hashWithSaltF
  {-# INLINE hash #-}

instance TestEquality (f (Expr t f)) => PC.TestEquality (Expr t f) where
  testEquality x y =
    case testEquality (eId x) (eId y) of
      Just Refl -> Just Refl
      Nothing ->
        if eHash x /= eHash y
        then Nothing
        else testEquality (eApp x) (eApp y)

instance PC.OrdF (f (Expr t f)) => PC.OrdF (Expr t f) where
  compareF x y =
    case testEquality (eId x) (eId y) of
      Just Refl -> PC.EQF
      Nothing -> PC.compareF (eApp x) (eApp y)

instance
  ( Eq (f (Expr t f) tp)
  , Ord (f (Expr t f) tp)
  , AD.Abstractable tp
  , HasBaseType (f (Expr t f))
  ) => Ord (Expr t f tp) where
  compare x y
    | eId x == eId y = EQ
    | eHash x /= eHash y = compare (eHash x) (eHash y)
    | otherwise = compare (eApp x) (eApp y)

-- | Return the expression with the larger hash.
-- Uses nonce ID as tiebreaker when hashes are equal.
-- Used to canonicalize commutative operations.
maxByHash :: Expr t f tp -> Expr t f tp -> Expr t f tp
maxByHash x y
  | eHash x < eHash y = y
  | eId x < eId y = y
  | otherwise = x
{-# INLINE maxByHash #-}

-- | Return the expression with the smaller hash.
-- Uses nonce ID as tiebreaker when hashes are equal.
-- Used to canonicalize commutative operations.
minByHash :: Expr t f tp -> Expr t f tp -> Expr t f tp
minByHash x y
  | eHash x < eHash y = x
  | eId x < eId y = x
  | otherwise = y
{-# INLINE minByHash #-}

-- | Pretty-print an expression given a pretty-printer for the app functor
pretty :: (forall tp'. f (Expr t f) tp' -> PP.Doc ann) -> Expr t f tp -> PP.Doc ann
pretty ppApp = ppApp . eApp
