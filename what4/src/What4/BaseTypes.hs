-----------------------------------------------------------------------
-- |
-- Module           : What4.BaseTypes
-- Description      : This module exports the types used in solver expressions.
-- Copyright        : (c) Galois, Inc 2014-2020
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module exports the types used in solver expressions.
--
-- These types are largely used as indexes to various GADTs and type
-- families as a way to let the GHC typechecker help us keep expressions
-- used by solvers apart.
--
-- In addition, we provide a value-level reification of the type
-- indices that can be examined by pattern matching, called 'BaseTypeRepr'.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds#-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module What4.BaseTypes
  ( -- * BaseType data kind
    type BaseType
    -- ** Constructors for kind BaseType
  , BaseBoolType
  , BaseIntegerType
  , BaseRealType
  , BaseStringType
  , BaseBVType
  , BaseFloatType
  , BaseComplexType
  , BaseStructType
  , BaseArrayType
    -- * StringInfo data kind
  , StringInfo
    -- ** Constructors for StringInfo
  , Char8
  , Char16
  , Unicode
    -- * FloatPrecision data kind
  , type FloatPrecision
  , type FloatPrecisionBits
    -- ** Constructors for kind FloatPrecision
  , FloatingPointPrecision
    -- ** FloatingPointPrecision aliases
  , Prec16
  , Prec32
  , Prec64
  , Prec80
  , Prec128
    -- * Representations of base types
  , BaseTypeRepr(..)
  , FloatPrecisionRepr(..)
  , StringInfoRepr(..)
  , arrayTypeIndices
  , arrayTypeResult
  , floatPrecisionToBVType
  , lemmaFloatPrecisionIsPos
  , module Data.Parameterized.NatRepr

    -- * KnownRepr
  , KnownRepr(..)  -- Re-export from 'Data.Parameterized.Classes'
  , KnownCtx
  ) where


import           Data.Hashable
import           Data.Kind
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           GHC.TypeNats as TypeNats
import           Prettyprinter

--------------------------------------------------------------------------------
-- KnownCtx

-- | A Context where all the argument types are 'KnownRepr' instances
type KnownCtx f = KnownRepr (Ctx.Assignment f)


------------------------------------------------------------------------
-- StringInfo

data StringInfo
     -- | 8-bit characters
   = Char8
     -- | 16-bit characters
   | Char16
     -- | Unicode code-points
   | Unicode


type Char8   = 'Char8   -- ^ @:: 'StringInfo'@.
type Char16  = 'Char16  -- ^ @:: 'StringInfo'@.
type Unicode = 'Unicode -- ^ @:: 'StringInfo'@.

------------------------------------------------------------------------
-- BaseType

-- | This data kind enumerates the Crucible solver interface types,
-- which are types that may be represented symbolically.
data BaseType
     -- | @BaseBoolType@ denotes Boolean values.
   = BaseBoolType
     -- | @BaseIntegerType@ denotes an integer.
   | BaseIntegerType
     -- | @BaseRealType@ denotes a real number.
   | BaseRealType
     -- | @BaseBVType n@ denotes a bitvector with @n@-bits.
   | BaseBVType TypeNats.Nat
     -- | @BaseFloatType fpp@ denotes a floating-point number with @fpp@
     -- precision.
   | BaseFloatType FloatPrecision
     -- | @BaseStringType@ denotes a sequence of Unicode codepoints
   | BaseStringType StringInfo
     -- | @BaseComplexType@ denotes a complex number with real components.
   | BaseComplexType
     -- | @BaseStructType tps@ denotes a sequence of values with types @tps@.
   | BaseStructType (Ctx.Ctx BaseType)
     -- | @BaseArrayType itps rtp@ denotes a function mapping indices @itps@
     -- to values of type @rtp@.
     --
     -- It does not have bounds as one would normally expect from an
     -- array in a programming language, but the solver does provide
     -- operations for doing pointwise updates.
   | BaseArrayType  (Ctx.Ctx BaseType) BaseType

type BaseBoolType    = 'BaseBoolType    -- ^ @:: 'BaseType'@.
type BaseIntegerType = 'BaseIntegerType -- ^ @:: 'BaseType'@.
type BaseRealType    = 'BaseRealType    -- ^ @:: 'BaseType'@.
type BaseBVType      = 'BaseBVType      -- ^ @:: 'TypeNats.Nat' -> 'BaseType'@.
type BaseFloatType   = 'BaseFloatType   -- ^ @:: 'FloatPrecision' -> 'BaseType'@.
type BaseStringType  = 'BaseStringType  -- ^ @:: 'BaseType'@.
type BaseComplexType = 'BaseComplexType -- ^ @:: 'BaseType'@.
type BaseStructType  = 'BaseStructType  -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'BaseType'@.
type BaseArrayType   = 'BaseArrayType   -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'BaseType' -> 'BaseType'@.

-- | This data kind describes the types of floating-point formats.
-- This consist of the standard IEEE 754-2008 binary floating point formats.
data FloatPrecision where
  FloatingPointPrecision :: TypeNats.Nat   -- number of bits for the exponent field
                         -> TypeNats.Nat   -- number of bits for the significand field
                         -> FloatPrecision
type FloatingPointPrecision = 'FloatingPointPrecision -- ^ @:: 'GHC.TypeNats.Nat' -> 'GHC.TypeNats.Nat' -> 'FloatPrecision'@.

-- | This computes the number of bits occupied by a floating-point format.
type family FloatPrecisionBits (fpp :: FloatPrecision) :: Nat where
  FloatPrecisionBits (FloatingPointPrecision eb sb) = eb + sb

-- | Floating-point precision aliases
type Prec16  = FloatingPointPrecision  5  11
type Prec32  = FloatingPointPrecision  8  24
type Prec64  = FloatingPointPrecision 11  53
type Prec80  = FloatingPointPrecision 15  65
type Prec128 = FloatingPointPrecision 15 113

------------------------------------------------------------------------
-- BaseTypeRepr

-- | A runtime representation of a solver interface type. Parameter @bt@
-- has kind 'BaseType'.
data BaseTypeRepr (bt::BaseType) :: Type where
   BaseBoolRepr    :: BaseTypeRepr BaseBoolType
   BaseBVRepr      :: (1 <= w) => !(NatRepr w) -> BaseTypeRepr (BaseBVType w)
   BaseIntegerRepr :: BaseTypeRepr BaseIntegerType
   BaseRealRepr    :: BaseTypeRepr BaseRealType
   BaseFloatRepr   :: !(FloatPrecisionRepr fpp) -> BaseTypeRepr (BaseFloatType fpp)
   BaseStringRepr  :: StringInfoRepr si -> BaseTypeRepr (BaseStringType si)
   BaseComplexRepr :: BaseTypeRepr BaseComplexType

   -- The representation of a struct type.
   BaseStructRepr :: !(Ctx.Assignment BaseTypeRepr ctx)
                  -> BaseTypeRepr (BaseStructType ctx)

   BaseArrayRepr :: !(Ctx.Assignment BaseTypeRepr (idx Ctx.::> tp))
                 -> !(BaseTypeRepr xs)
                 -> BaseTypeRepr (BaseArrayType (idx Ctx.::> tp) xs)

data FloatPrecisionRepr (fpp :: FloatPrecision) where
  FloatingPointPrecisionRepr
    :: (2 <= eb, 2 <= sb)
    => !(NatRepr eb)
    -> !(NatRepr sb)
    -> FloatPrecisionRepr (FloatingPointPrecision eb sb)

data StringInfoRepr (si::StringInfo) where
  Char8Repr     :: StringInfoRepr Char8
  Char16Repr    :: StringInfoRepr Char16
  UnicodeRepr   :: StringInfoRepr Unicode

-- | Return the type of the indices for an array type.
arrayTypeIndices :: BaseTypeRepr (BaseArrayType idx tp)
                 -> Ctx.Assignment BaseTypeRepr idx
arrayTypeIndices (BaseArrayRepr i _) = i

-- | Return the result type of an array type.
arrayTypeResult :: BaseTypeRepr (BaseArrayType idx tp) -> BaseTypeRepr tp
arrayTypeResult (BaseArrayRepr _ rtp) = rtp

floatPrecisionToBVType
  :: FloatPrecisionRepr (FloatingPointPrecision eb sb)
  -> BaseTypeRepr (BaseBVType (eb + sb))
floatPrecisionToBVType fpp@(FloatingPointPrecisionRepr eb sb)
  | LeqProof <- lemmaFloatPrecisionIsPos fpp
  = BaseBVRepr $ addNat eb sb

lemmaFloatPrecisionIsPos
  :: forall eb' sb'
   . FloatPrecisionRepr (FloatingPointPrecision eb' sb')
  -> LeqProof 1 (eb' + sb')
lemmaFloatPrecisionIsPos (FloatingPointPrecisionRepr eb sb)
  | LeqProof <- leqTrans (LeqProof @1 @2) (LeqProof @2 @eb')
  , LeqProof <- leqTrans (LeqProof @1 @2) (LeqProof @2 @sb')
  = leqAddPos eb sb

instance KnownRepr BaseTypeRepr BaseBoolType where
  knownRepr = BaseBoolRepr
instance KnownRepr BaseTypeRepr BaseIntegerType where
  knownRepr = BaseIntegerRepr
instance KnownRepr BaseTypeRepr BaseRealType where
  knownRepr = BaseRealRepr
instance KnownRepr StringInfoRepr si => KnownRepr BaseTypeRepr (BaseStringType si) where
  knownRepr = BaseStringRepr knownRepr
instance (1 <= w, KnownNat w) => KnownRepr BaseTypeRepr (BaseBVType w) where
  knownRepr = BaseBVRepr knownNat
instance (KnownRepr FloatPrecisionRepr fpp) => KnownRepr BaseTypeRepr (BaseFloatType fpp) where
  knownRepr = BaseFloatRepr knownRepr
instance KnownRepr BaseTypeRepr BaseComplexType where
  knownRepr = BaseComplexRepr

instance KnownRepr (Ctx.Assignment BaseTypeRepr) ctx
      => KnownRepr BaseTypeRepr (BaseStructType ctx) where
  knownRepr = BaseStructRepr knownRepr

instance ( KnownRepr (Ctx.Assignment BaseTypeRepr) idx
         , KnownRepr BaseTypeRepr tp
         , KnownRepr BaseTypeRepr t
         )
      => KnownRepr BaseTypeRepr (BaseArrayType (idx Ctx.::> tp) t) where
  knownRepr = BaseArrayRepr knownRepr knownRepr

instance (2 <= eb, 2 <= es, KnownNat eb, KnownNat es) => KnownRepr FloatPrecisionRepr (FloatingPointPrecision eb es) where
  knownRepr = FloatingPointPrecisionRepr knownNat knownNat

instance KnownRepr StringInfoRepr Char8 where
  knownRepr = Char8Repr
instance KnownRepr StringInfoRepr Char16 where
  knownRepr = Char16Repr
instance KnownRepr StringInfoRepr Unicode where
  knownRepr = UnicodeRepr


-- Force BaseTypeRepr, etc. to be in context for next slice.
$(return [])

instance HashableF BaseTypeRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (BaseTypeRepr bt) where
  hashWithSalt = $(structuralHashWithSalt [t|BaseTypeRepr|] [])

instance HashableF FloatPrecisionRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (FloatPrecisionRepr fpp) where
  hashWithSalt = $(structuralHashWithSalt [t|FloatPrecisionRepr|] [])

instance HashableF StringInfoRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (StringInfoRepr si) where
  hashWithSalt = $(structuralHashWithSalt [t|StringInfoRepr|] [])

instance Pretty (BaseTypeRepr bt) where
  pretty = viaShow
instance Show (BaseTypeRepr bt) where
  showsPrec = $(structuralShowsPrec [t|BaseTypeRepr|])
instance ShowF BaseTypeRepr

instance Pretty (FloatPrecisionRepr fpp) where
  pretty (FloatingPointPrecisionRepr exp' sig) = 
    parens ("FloatingPrecision" <+> (pretty $ natValue exp') <+> (pretty $ natValue sig))

instance Show (FloatPrecisionRepr fpp) where
  showsPrec = $(structuralShowsPrec [t|FloatPrecisionRepr|])
instance ShowF FloatPrecisionRepr

-- | Prints string type reprs, matching the syntax of crucible atoms https://github.com/GaloisInc/crucible/blob/a2502010cab0de44ec4c3b802453dc1009181d6b/crucible-syntax/src/Lang/Crucible/Syntax/Atoms.hs#L148-L151
instance Pretty (StringInfoRepr si) where
  pretty UnicodeRepr = "Unicode"
  pretty Char16Repr = "Char16"
  pretty Char8Repr = "Char8"

instance Show (StringInfoRepr si) where
  showsPrec = $(structuralShowsPrec [t|StringInfoRepr|])
instance ShowF StringInfoRepr

instance TestEquality BaseTypeRepr where
  testEquality = $(structuralTypeEquality [t|BaseTypeRepr|]
                   [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
                   , (TypeApp (ConType [t|FloatPrecisionRepr|]) AnyType, [|testEquality|])
                   , (TypeApp (ConType [t|StringInfoRepr|]) AnyType, [|testEquality|])
                   , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
                   , ( TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|testEquality|]
                     )
                   ]
                  )
instance Eq (BaseTypeRepr bt) where
  x == y = isJust (testEquality x y)

instance OrdF BaseTypeRepr where
  compareF = $(structuralTypeOrd [t|BaseTypeRepr|]
                   [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|compareF|])
                   , (TypeApp (ConType [t|FloatPrecisionRepr|]) AnyType, [|compareF|])
                   , (TypeApp (ConType [t|StringInfoRepr|]) AnyType, [|compareF|])
                   , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|compareF|])
                   , (TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|compareF|]
                     )
                   ]
                  )

instance TestEquality FloatPrecisionRepr where
  testEquality = $(structuralTypeEquality [t|FloatPrecisionRepr|]
      [(TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])]
    )
instance Eq (FloatPrecisionRepr fpp) where
  x == y = isJust (testEquality x y)
instance OrdF FloatPrecisionRepr where
  compareF = $(structuralTypeOrd [t|FloatPrecisionRepr|]
      [(TypeApp (ConType [t|NatRepr|]) AnyType, [|compareF|])]
    )

instance TestEquality StringInfoRepr where
  testEquality = $(structuralTypeEquality [t|StringInfoRepr|] [])
instance Eq (StringInfoRepr si) where
  x == y = isJust (testEquality x y)
instance OrdF StringInfoRepr where
  compareF = $(structuralTypeOrd [t|StringInfoRepr|] [])
