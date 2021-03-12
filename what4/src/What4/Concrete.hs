-----------------------------------------------------------------------
-- |
-- Module           : What4.Concrete
-- Description      : Concrete values of base types
-- Copyright        : (c) Galois, Inc 2018-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module defines a representation of concrete values of base
-- types.  These are values in fully-evaluated form that do not depend
-- on any symbolic constants.
-----------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.Concrete
  (
    -- * Concrete values
    ConcreteVal(..)
  , concreteType
  , ppConcrete

    -- * Concrete projections
  , fromConcreteBool
  , fromConcreteInteger
  , fromConcreteReal
  , fromConcreteString
  , fromConcreteBV
  , fromConcreteComplex
  ) where

import qualified Data.List as List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Numeric as N
import qualified Prettyprinter as PP

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC

import           What4.BaseTypes
import           What4.Utils.Complex
import           What4.Utils.StringLiteral

-- | A data type for representing the concrete values of base types.
data ConcreteVal tp where
  ConcreteBool    :: Bool -> ConcreteVal BaseBoolType
  ConcreteInteger :: Integer -> ConcreteVal BaseIntegerType
  ConcreteReal    :: Rational -> ConcreteVal BaseRealType
  ConcreteString  :: StringLiteral si -> ConcreteVal (BaseStringType si)
  ConcreteComplex :: Complex Rational -> ConcreteVal BaseComplexType
  ConcreteBV      ::
    (1 <= w) =>
    NatRepr w {- Width of the bitvector -} ->
    BV.BV w   {- Unsigned value of the bitvector -} ->
    ConcreteVal (BaseBVType w)
  ConcreteStruct  :: Ctx.Assignment ConcreteVal ctx -> ConcreteVal (BaseStructType ctx)
  ConcreteArray   ::
    Ctx.Assignment BaseTypeRepr (idx ::> i) {- Type representatives for the index tuple -} ->
    ConcreteVal b {- A default value -} ->
    Map (Ctx.Assignment ConcreteVal (idx ::> i)) (ConcreteVal b) {- A collection of point-updates -} ->
    ConcreteVal (BaseArrayType (idx ::> i) b)

deriving instance ShowF ConcreteVal
deriving instance Show (ConcreteVal tp)

fromConcreteBool :: ConcreteVal BaseBoolType -> Bool
fromConcreteBool (ConcreteBool x) = x

fromConcreteInteger :: ConcreteVal BaseIntegerType -> Integer
fromConcreteInteger (ConcreteInteger x) = x

fromConcreteReal :: ConcreteVal BaseRealType -> Rational
fromConcreteReal (ConcreteReal x) = x

fromConcreteComplex :: ConcreteVal BaseComplexType -> Complex Rational
fromConcreteComplex (ConcreteComplex x) = x

fromConcreteString :: ConcreteVal (BaseStringType si) -> StringLiteral si
fromConcreteString (ConcreteString x) = x

fromConcreteBV :: ConcreteVal (BaseBVType w) -> BV.BV w
fromConcreteBV (ConcreteBV _w x) = x

-- | Compute the type representative for a concrete value.
concreteType :: ConcreteVal tp -> BaseTypeRepr tp
concreteType = \case
  ConcreteBool{}     -> BaseBoolRepr
  ConcreteInteger{}  -> BaseIntegerRepr
  ConcreteReal{}     -> BaseRealRepr
  ConcreteString s   -> BaseStringRepr (stringLiteralInfo s)
  ConcreteComplex{}  -> BaseComplexRepr
  ConcreteBV w _     -> BaseBVRepr w
  ConcreteStruct xs  -> BaseStructRepr (fmapFC concreteType xs)
  ConcreteArray idxTy def _ -> BaseArrayRepr idxTy (concreteType def)

$(return [])

instance TestEquality ConcreteVal where
  testEquality = $(structuralTypeEquality [t|ConcreteVal|]
     [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|testEquality|])
     , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType, [|testEqualityFC testEquality|])
     , (ConType [t|ConcreteVal|] `TypeApp` AnyType, [|testEquality|])
     , (ConType [t|StringLiteral|] `TypeApp` AnyType, [|testEquality|])
     , (ConType [t|Map|] `TypeApp` AnyType `TypeApp` AnyType, [|\x y -> if x == y then Just Refl else Nothing|])
     ])

instance Eq (ConcreteVal tp) where
  x==y = isJust (testEquality x y)

instance OrdF ConcreteVal where
  compareF = $(structuralTypeOrd [t|ConcreteVal|]
     [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|compareF|])
     , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType, [|compareFC compareF|])
     , (ConType [t|ConcreteVal|] `TypeApp` AnyType, [|compareF|])
     , (ConType [t|StringLiteral|] `TypeApp` AnyType, [|compareF|])
     , (ConType [t|Map|] `TypeApp` AnyType `TypeApp` AnyType, [|\x y -> fromOrdering (compare x y)|])
     ])

instance Ord (ConcreteVal tp) where
  compare x y = toOrdering (compareF x y)

-- | Pretty-print a rational number.
ppRational :: Rational -> PP.Doc ann
ppRational = PP.viaShow

-- | Pretty-print a concrete value
ppConcrete :: ConcreteVal tp -> PP.Doc ann
ppConcrete = \case
  ConcreteBool x -> PP.pretty x
  ConcreteInteger x -> PP.pretty x
  ConcreteReal x -> ppRational x
  ConcreteString x -> PP.viaShow x
  ConcreteBV w x -> PP.pretty ("0x" ++ (N.showHex (BV.asUnsigned x) (":[" ++ show w ++ "]")))
  ConcreteComplex (r :+ i) -> PP.pretty "complex(" PP.<> ppRational r PP.<> PP.pretty ", " PP.<> ppRational i PP.<> PP.pretty ")"
  ConcreteStruct xs -> PP.pretty "struct(" PP.<> PP.cat (List.intersperse PP.comma (toListFC ppConcrete xs)) PP.<> PP.pretty ")"
  ConcreteArray _ def xs0 -> go (Map.toAscList xs0) (PP.pretty "constArray(" PP.<> ppConcrete def PP.<> PP.pretty ")")
    where
    go  [] doc = doc
    go ((i,x):xs) doc = ppUpd i x (go xs doc)

    ppUpd i x doc =
       PP.pretty "update(" PP.<> PP.cat (List.intersperse PP.comma (toListFC ppConcrete i))
                         PP.<> PP.comma
                         PP.<> ppConcrete x
                         PP.<> PP.comma
                         PP.<> doc
                         PP.<> PP.pretty ")"
