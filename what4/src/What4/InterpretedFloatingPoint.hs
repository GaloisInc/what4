{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module What4.InterpretedFloatingPoint
  ( -- * FloatInfo data kind
    type FloatInfo
    -- ** Constructors for kind FloatInfo
  , HalfFloat
  , SingleFloat
  , DoubleFloat
  , QuadFloat
  , X86_80Float
  , DoubleDoubleFloat
    -- ** Representations of FloatInfo types
  , FloatInfoRepr(..)
    -- * extended 80 bit float values ("long double")
  , X86_80Val(..)
  , fp80ToBits
  , fp80ToRational
    -- * FloatInfo to/from FloatPrecision
  , FloatInfoToPrecision
  , FloatPrecisionToInfo
  , floatInfoToPrecisionRepr
  , floatPrecisionToInfoRepr
    -- * Bit-width type family
  , FloatInfoToBitWidth
  , floatInfoToBVTypeRepr
    -- * FloatMode
  , type FloatMode
  , FloatModeRepr(..)
  , FloatIEEE
  , FloatUninterpreted
  , FloatReal

    -- * Interface classes
  , SymInterpretedFloat
  , IsInterpretedFloatExprBuilder(..)
  , IsInterpretedFloatSymExprBuilder(..)
  ) where

import qualified Data.Binary.IEEE754 as IEEE754
import qualified Data.BitVector.Sized as BV
import Data.Bits
import Data.Hashable
import Data.Kind
import Data.Parameterized.Classes
import Data.Parameterized.TH.GADT
import Data.Ratio
import Data.Word ( Word16, Word64 )
import GHC.TypeNats
import Text.PrettyPrint.ANSI.Leijen

import Data.Parameterized.Context as Ctx

import What4.BaseTypes
import What4.Interface

-- | This data kind describes the types of floating-point formats.
-- This consist of the standard IEEE 754-2008 binary floating point formats,
-- as well as the X86 extended 80-bit format and the double-double format.
data FloatInfo where
  HalfFloat         :: FloatInfo  --  16 bit binary IEEE754
  SingleFloat       :: FloatInfo  --  32 bit binary IEEE754
  DoubleFloat       :: FloatInfo  --  64 bit binary IEEE754
  QuadFloat         :: FloatInfo  -- 128 bit binary IEEE754
  X86_80Float       :: FloatInfo  -- X86 80-bit extended floats
  DoubleDoubleFloat :: FloatInfo  -- two 64-bit floats fused in the "double-double" style

type HalfFloat         = 'HalfFloat         -- ^  16 bit binary IEEE754.
type SingleFloat       = 'SingleFloat       -- ^  32 bit binary IEEE754.
type DoubleFloat       = 'DoubleFloat       -- ^  64 bit binary IEEE754.
type QuadFloat         = 'QuadFloat         -- ^ 128 bit binary IEEE754.
type X86_80Float       = 'X86_80Float       -- ^ X86 80-bit extended floats.
type DoubleDoubleFloat = 'DoubleDoubleFloat -- ^ Two 64-bit floats fused in the "double-double" style.

-- | A family of value-level representatives for floating-point types.
data FloatInfoRepr (fi :: FloatInfo) where
  HalfFloatRepr         :: FloatInfoRepr HalfFloat
  SingleFloatRepr       :: FloatInfoRepr SingleFloat
  DoubleFloatRepr       :: FloatInfoRepr DoubleFloat
  QuadFloatRepr         :: FloatInfoRepr QuadFloat
  X86_80FloatRepr       :: FloatInfoRepr X86_80Float
  DoubleDoubleFloatRepr :: FloatInfoRepr DoubleDoubleFloat

instance KnownRepr FloatInfoRepr HalfFloat         where knownRepr = HalfFloatRepr
instance KnownRepr FloatInfoRepr SingleFloat       where knownRepr = SingleFloatRepr
instance KnownRepr FloatInfoRepr DoubleFloat       where knownRepr = DoubleFloatRepr
instance KnownRepr FloatInfoRepr QuadFloat         where knownRepr = QuadFloatRepr
instance KnownRepr FloatInfoRepr X86_80Float       where knownRepr = X86_80FloatRepr
instance KnownRepr FloatInfoRepr DoubleDoubleFloat where knownRepr = DoubleDoubleFloatRepr


-- | Mode flag for how floating-point values should be interpreted.
data FloatMode where
  FloatIEEE :: FloatMode
  FloatUninterpreted :: FloatMode
  FloatReal :: FloatMode
type FloatIEEE = 'FloatIEEE
type FloatUninterpreted = 'FloatUninterpreted
type FloatReal = 'FloatReal


data FloatModeRepr :: FloatMode -> Type where
  FloatIEEERepr          :: FloatModeRepr FloatIEEE
  FloatUninterpretedRepr :: FloatModeRepr FloatUninterpreted
  FloatRealRepr          :: FloatModeRepr FloatReal

instance Show (FloatModeRepr fm) where
  showsPrec _ FloatIEEERepr          = showString "FloatIEEE"
  showsPrec _ FloatUninterpretedRepr = showString "FloatUninterpreted"
  showsPrec _ FloatRealRepr          = showString "FloatReal"

instance ShowF FloatModeRepr

instance KnownRepr FloatModeRepr FloatIEEE          where knownRepr = FloatIEEERepr
instance KnownRepr FloatModeRepr FloatUninterpreted where knownRepr = FloatUninterpretedRepr
instance KnownRepr FloatModeRepr FloatReal          where knownRepr = FloatRealRepr

instance TestEquality FloatModeRepr where
  testEquality FloatIEEERepr           FloatIEEERepr           = return Refl
  testEquality FloatUninterpretedRepr  FloatUninterpretedRepr  = return Refl
  testEquality FloatRealRepr           FloatRealRepr           = return Refl
  testEquality _ _ = Nothing



$(return [])

instance HashableF FloatInfoRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (FloatInfoRepr fi) where
  hashWithSalt = $(structuralHashWithSalt [t|FloatInfoRepr|] [])

instance Pretty (FloatInfoRepr fi) where
  pretty = text . show
instance Show (FloatInfoRepr fi) where
  showsPrec = $(structuralShowsPrec [t|FloatInfoRepr|])
instance ShowF FloatInfoRepr

instance TestEquality FloatInfoRepr where
  testEquality = $(structuralTypeEquality [t|FloatInfoRepr|] [])
instance OrdF FloatInfoRepr where
  compareF = $(structuralTypeOrd [t|FloatInfoRepr|] [])


type family FloatInfoToPrecision (fi :: FloatInfo) :: FloatPrecision where
  FloatInfoToPrecision HalfFloat   = Prec16
  FloatInfoToPrecision SingleFloat = Prec32
  FloatInfoToPrecision DoubleFloat = Prec64
  FloatInfoToPrecision X86_80Float = Prec80
  FloatInfoToPrecision QuadFloat   = Prec128

type family FloatPrecisionToInfo (fpp :: FloatPrecision) :: FloatInfo where
  FloatPrecisionToInfo Prec16  = HalfFloat
  FloatPrecisionToInfo Prec32  = SingleFloat
  FloatPrecisionToInfo Prec64  = DoubleFloat
  FloatPrecisionToInfo Prec80  = X86_80Float
  FloatPrecisionToInfo Prec128 = QuadFloat

type family FloatInfoToBitWidth (fi :: FloatInfo) :: GHC.TypeNats.Nat where
  FloatInfoToBitWidth HalfFloat         = 16
  FloatInfoToBitWidth SingleFloat       = 32
  FloatInfoToBitWidth DoubleFloat       = 64
  FloatInfoToBitWidth X86_80Float       = 80
  FloatInfoToBitWidth QuadFloat         = 128
  FloatInfoToBitWidth DoubleDoubleFloat = 128

floatInfoToPrecisionRepr
  :: FloatInfoRepr fi -> FloatPrecisionRepr (FloatInfoToPrecision fi)
floatInfoToPrecisionRepr = \case
  HalfFloatRepr         -> knownRepr
  SingleFloatRepr       -> knownRepr
  DoubleFloatRepr       -> knownRepr
  QuadFloatRepr         -> knownRepr
  X86_80FloatRepr       -> knownRepr -- n.b. semantics TBD, not technically an IEEE-754 format.
  DoubleDoubleFloatRepr -> error "double-double is not an IEEE-754 format."

floatPrecisionToInfoRepr
  :: FloatPrecisionRepr fpp -> FloatInfoRepr (FloatPrecisionToInfo fpp)
floatPrecisionToInfoRepr fpp
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec16)
  = knownRepr
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec32)
  = knownRepr
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec64)
  = knownRepr
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec80)
  = knownRepr
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec128)
  = knownRepr
  | otherwise
  = error $ "unexpected IEEE-754 precision: " ++ show fpp

floatInfoToBVTypeRepr
  :: FloatInfoRepr fi -> BaseTypeRepr (BaseBVType (FloatInfoToBitWidth fi))
floatInfoToBVTypeRepr = \case
  HalfFloatRepr         -> knownRepr
  SingleFloatRepr       -> knownRepr
  DoubleFloatRepr       -> knownRepr
  QuadFloatRepr         -> knownRepr
  X86_80FloatRepr       -> knownRepr
  DoubleDoubleFloatRepr -> knownRepr


-- | Representation of 80-bit floating values, since there's no native
-- Haskell type for these.
data X86_80Val = X86_80Val
                 Word16 -- exponent
                 Word64 -- significand
               deriving (Show, Eq, Ord)

fp80ToBits :: X86_80Val -> Integer
fp80ToBits (X86_80Val ex mantissa) =
  shiftL (toInteger ex) 64 .|. toInteger mantissa

fp80ToRational :: X86_80Val -> Maybe Rational
fp80ToRational (X86_80Val ex mantissa)
    -- infinities/NaN/etc
  | ex' == 0x7FFF = Nothing

    -- denormal/pseudo-denormal/normal/unnormal numbers
  | otherwise = Just $! (if s then negate else id) (m * (1 % 2^e))

  where
  s   = testBit ex 15
  ex' = ex .&. 0x7FFF
  m   = (toInteger mantissa) % ((2::Integer)^(63::Integer))
  e   = 16382 - toInteger ex'

-- Note that the long-double package also provides a representation
-- for 80-bit floating point values but that package includes
-- significant FFI compatibility elements which may not be necessary
-- here; in the future that could be used by defining 'type X86_80Val
-- = LongDouble'.

-- | Interpretation of the floating point type.
type family SymInterpretedFloatType (fm ::FloatMode) (fi::FloatInfo) :: BaseType

-- | Symbolic floating point numbers.
type SymInterpretedFloat sym fm fi = SymExpr sym (SymInterpretedFloatType fm fi)

-- | Abstact floating point operations.
class IsExprBuilder sym => IsInterpretedFloatExprBuilder (sym ::Type) (fm :: FloatMode) where
  -- | Return floating point number @+0@.
  iFloatPZero :: sym -> FloatModeRepr fm -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fm fi)

  -- | Return floating point number @-0@.
  iFloatNZero :: sym -> FloatModeRepr fm -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fm fi)

  -- |  Return floating point NaN.
  iFloatNaN :: sym -> FloatModeRepr fm -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fm fi)

  -- | Return floating point @+infinity@.
  iFloatPInf :: sym -> FloatModeRepr fm -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fm fi)

  -- | Return floating point @-infinity@.
  iFloatNInf :: sym -> FloatModeRepr fm -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fm fi)

  -- | Create a floating point literal from a rational literal.
  iFloatLit
    :: sym -> FloatModeRepr fm -> FloatInfoRepr fi -> Rational -> IO (SymInterpretedFloat sym fm fi)

  -- | Create a (single precision) floating point literal.
  iFloatLitSingle :: sym -> FloatModeRepr fm -> Float -> IO (SymInterpretedFloat sym fm SingleFloat)
  -- | Create a (double precision) floating point literal.
  iFloatLitDouble :: sym -> FloatModeRepr fm -> Double -> IO (SymInterpretedFloat sym fm DoubleFloat)
  -- | Create an (extended double precision) floating point literal.
  iFloatLitLongDouble :: sym -> FloatModeRepr fm -> X86_80Val -> IO (SymInterpretedFloat sym fm X86_80Float)

  -- | Negate a floating point number.
  iFloatNeg
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Return the absolute value of a floating point number.
  iFloatAbs
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Compute the square root of a floating point number.
  iFloatSqrt
    :: sym
    -> FloatModeRepr fm
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Add two floating point numbers.
  iFloatAdd
    :: sym
    -> FloatModeRepr fm
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Subtract two floating point numbers.
  iFloatSub
    :: sym
    -> FloatModeRepr fm
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Multiply two floating point numbers.
  iFloatMul
    :: sym
    -> FloatModeRepr fm
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Divide two floating point numbers.
  iFloatDiv
    :: sym
    -> FloatModeRepr fm
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Compute the reminder: @x - y * n@, where @n@ in Z is nearest to @x / y@.
  iFloatRem
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Return the min of two floating point numbers.
  iFloatMin
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Return the max of two floating point numbers.
  iFloatMax
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Compute the fused multiplication and addition: @(x * y) + z@.
  iFloatFMA
    :: sym
    -> FloatModeRepr fm
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Check logical equality of two floating point numbers.
  iFloatEq
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  -- | Check logical non-equality of two floating point numbers.
  iFloatNe
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  -- | Check IEEE equality of two floating point numbers.
  iFloatFpEq
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  -- | Check IEEE non-equality of two floating point numbers.
  iFloatFpNe
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  -- | Check @<=@ on two floating point numbers.
  iFloatLe
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  -- | Check @<@ on two floating point numbers.
  iFloatLt
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  -- | Check @>=@ on two floating point numbers.
  iFloatGe
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  -- | Check @>@ on two floating point numbers.
  iFloatGt
    :: sym
    -> FloatModeRepr fm
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (Pred sym)

  iFloatIsNaN :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (Pred sym)
  iFloatIsInf :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (Pred sym)
  iFloatIsZero :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (Pred sym)
  iFloatIsPos :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (Pred sym)
  iFloatIsNeg :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (Pred sym)
  iFloatIsSubnorm :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (Pred sym)
  iFloatIsNorm :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (Pred sym)

  -- | If-then-else on floating point numbers.
  iFloatIte
    :: sym
    -> FloatModeRepr fm
    -> Pred sym
    -> SymInterpretedFloat sym fm fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)

  -- | Change the precision of a floating point number.
  iFloatCast
    :: sym
    -> FloatModeRepr fm
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi'
    -> IO (SymInterpretedFloat sym fm fi)
  -- | Round a floating point number to an integral value.
  iFloatRound
    :: sym
    -> FloatModeRepr fm
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> IO (SymInterpretedFloat sym fm fi)
  -- | Convert from binary representation in IEEE 754-2008 format to
  --   floating point.
  iFloatFromBinary
    :: sym
    -> FloatModeRepr fm
    -> FloatInfoRepr fi
    -> SymBV sym (FloatInfoToBitWidth fi)
    -> IO (SymInterpretedFloat sym fm fi)
  -- | Convert from floating point from to the binary representation in
  --   IEEE 754-2008 format.
  iFloatToBinary
    :: sym
    -> FloatModeRepr fm
    -> FloatInfoRepr fi
    -> SymInterpretedFloat sym fm fi
    -> IO (SymBV sym (FloatInfoToBitWidth fi))
  -- | Convert a unsigned bitvector to a floating point number.
  iBVToFloat
    :: (1 <= w)
    => sym
    -> FloatModeRepr fm
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymBV sym w
    -> IO (SymInterpretedFloat sym fm fi)
  -- | Convert a signed bitvector to a floating point number.
  iSBVToFloat
    :: (1 <= w) => sym
    -> FloatModeRepr fm
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymBV sym w
    -> IO (SymInterpretedFloat sym fm fi)
  -- | Convert a real number to a floating point number.
  iRealToFloat
    :: sym
    -> FloatModeRepr fm
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymReal sym
    -> IO (SymInterpretedFloat sym fm fi)
  -- | Convert a floating point number to a unsigned bitvector.
  iFloatToBV
    :: (1 <= w)
    => sym
    -> FloatModeRepr fm
    -> NatRepr w
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> IO (SymBV sym w)
  -- | Convert a floating point number to a signed bitvector.
  iFloatToSBV
    :: (1 <= w)
    => sym
    -> FloatModeRepr fm
    -> NatRepr w
    -> RoundingMode
    -> SymInterpretedFloat sym fm fi
    -> IO (SymBV sym w)
  -- | Convert a floating point number to a real number.
  iFloatToReal :: sym -> FloatModeRepr fm -> SymInterpretedFloat sym fm fi -> IO (SymReal sym)

  -- | The associated BaseType representative of the floating point
  -- interpretation for each format.
  iFloatBaseTypeRepr
    :: sym
    -> FloatModeRepr fm
    -> FloatInfoRepr fi
    -> BaseTypeRepr (SymInterpretedFloatType fm fi)

-- | Helper interface for creating new symbolic floating-point constants and
--   variables.
class (IsSymExprBuilder sym, IsInterpretedFloatExprBuilder sym fm) => IsInterpretedFloatSymExprBuilder sym fm where
  -- | Create a fresh top-level floating-point uninterpreted constant.
  freshFloatConstant
    :: sym
    -> FloatModeRepr fm
    -> SolverSymbol
    -> FloatInfoRepr fi
    -> IO (SymInterpretedFloat sym fm fi)
  freshFloatConstant sym fm nm fi = freshConstant sym nm $ iFloatBaseTypeRepr sym fm fi

  -- | Create a fresh floating-point latch variable.
  freshFloatLatch
    :: sym
    -> FloatModeRepr fm
    -> SolverSymbol
    -> FloatInfoRepr fi
    -> IO (SymInterpretedFloat sym fm fi)
  freshFloatLatch sym fm nm fi = freshLatch sym nm $ iFloatBaseTypeRepr sym fm fi

  -- | Creates a floating-point bound variable.
  freshFloatBoundVar
    :: sym
    -> FloatModeRepr fm
    -> SolverSymbol
    -> FloatInfoRepr fi
    -> IO (BoundVar sym (SymInterpretedFloatType fm fi))
  freshFloatBoundVar sym fm nm fi = freshBoundVar sym nm $ iFloatBaseTypeRepr sym fm fi



----------------------------------------------------------------------
-- Float interpretations

type instance SymInterpretedFloatType FloatReal fi = BaseRealType

instance IsSymExprBuilder sym => IsInterpretedFloatExprBuilder sym FloatReal where
  iFloatPZero sym _ _ = return $ realZero sym
  iFloatNZero sym _ _ = return $ realZero sym
  iFloatNaN _ _ _ = fail "NaN cannot be represented as a real value."
  iFloatPInf _ _ _ = fail "+Infinity cannot be represented as a real value."
  iFloatNInf _ _ _ = fail "-Infinity cannot be represented as a real value."
  iFloatLit sym _ _ = realLit sym
  iFloatLitSingle sym _ = realLit sym . toRational
  iFloatLitDouble sym _ = realLit sym . toRational
  iFloatLitLongDouble sym _ x =
     case fp80ToRational x of
       Nothing -> fail ("80-bit floating point value does not represent a rational number: " ++ show x)
       Just r  -> realLit sym r
  iFloatNeg sym _ = realNeg sym
  iFloatAbs sym _ = realAbs sym
  iFloatSqrt sym _ _ = realSqrt sym
  iFloatAdd sym _ _ = realAdd sym
  iFloatSub sym _ _ = realSub sym
  iFloatMul sym _ _ = realMul sym
  iFloatDiv sym _ _ = realDiv sym
  iFloatRem sym _ = realMod sym
  iFloatMin sym _ x y = do
    c <- realLe sym x y
    realIte sym c x y
  iFloatMax sym _ x y = do
    c <- realGe sym x y
    realIte sym c x y
  iFloatFMA sym _ _ x y z = do
    tmp <- (realMul sym x y)
    realAdd sym tmp z
  iFloatEq sym _ = realEq sym
  iFloatNe sym _ = realNe sym
  iFloatFpEq sym _ = realEq sym
  iFloatFpNe sym _ = realNe sym
  iFloatLe sym _ = realLe sym
  iFloatLt sym _ = realLt sym
  iFloatGe sym _ = realGe sym
  iFloatGt sym _ = realGt sym
  iFloatIte sym _ = realIte sym
  iFloatIsNaN sym _ _ = return $ falsePred sym
  iFloatIsInf sym _ _ = return $ falsePred sym
  iFloatIsZero sym _ = realEq sym $ realZero sym
  iFloatIsPos sym _ = realLt sym $ realZero sym
  iFloatIsNeg sym _ = realGt sym $ realZero sym
  iFloatIsSubnorm sym _ _ = return $ falsePred sym
  iFloatIsNorm sym _ = realNe sym $ realZero sym
  iFloatCast _ _ _ _ = return
  iFloatRound sym _ r x =
    integerToReal sym =<< case r of
      RNA -> realRound sym x
      RTP -> realCeil sym x
      RTN -> realFloor sym x
      RTZ -> do
        is_pos <- realLt sym (realZero sym) x
        iteM intIte sym is_pos (realFloor sym x) (realCeil sym x)
      RNE -> fail "Unsupported round to nearest even for real values."

  iFloatFromBinary sym _ _ x
      | SomeFnApp fn args <- asFnApp sym x
      , (Ctx.Empty Ctx.:> BaseRealRepr Ctx.:> BaseIntegerRepr) <- fnArgTypes fn
      , BaseBVRepr w <- fnReturnType fn
      , (Ctx.Empty Ctx.:> rval :> _i) <- args
      = do fn' <- symFnByName sym "uninterpreted_real_to_float_binary"
                    (Ctx.Empty Ctx.:> BaseRealRepr Ctx.:> BaseIntegerRepr)
                    (BaseBVRepr w)
           case fnTestEq fn fn' of
             Just (Refl, Refl) -> return rval
             Nothing   -> fallback
      | otherwise = fallback

    where
    fallback =
        mkUninterpFnApp sym
            "uninterpreted_real_from_float_binary"
            (Ctx.Empty Ctx.:> x)
            BaseRealRepr

  iFloatToBinary sym _ fi x =
    do i <- freshConstant sym emptySymbol BaseIntegerRepr
       mkUninterpFnApp sym
          "uninterpreted_real_to_float_binary"
          (Ctx.Empty Ctx.:> x Ctx.:> i)
          (floatInfoToBVTypeRepr fi)

  iBVToFloat sym _ _ _ = uintToReal sym
  iSBVToFloat sym _ _ _ = sbvToReal sym
  iRealToFloat _ _ _ _ = return
  iFloatToBV sym _ w _ x = realToBV sym x w
  iFloatToSBV sym _ w _ x = realToSBV sym x w
  iFloatToReal _ _ = return
  iFloatBaseTypeRepr _ _ _ = knownRepr


type instance SymInterpretedFloatType FloatUninterpreted fi = BaseBVType (FloatInfoToBitWidth fi)

instance IsSymExprBuilder sym => IsInterpretedFloatExprBuilder sym FloatUninterpreted where
  iFloatPZero sym fm fi =
    floatUninterpArithCt "uninterpreted_float_pzero" sym $ iFloatBaseTypeRepr sym fm fi
  iFloatNZero sym fm fi =
    floatUninterpArithCt "uninterpreted_float_nzero" sym $ iFloatBaseTypeRepr sym fm fi
  iFloatNaN sym fm fi =
    floatUninterpArithCt "uninterpreted_float_nan" sym $ iFloatBaseTypeRepr sym fm fi
  iFloatPInf sym fm fi =
    floatUninterpArithCt "uninterpreted_float_pinf" sym $ iFloatBaseTypeRepr sym fm fi
  iFloatNInf sym fm fi =
    floatUninterpArithCt "uninterpreted_float_ninf" sym $ iFloatBaseTypeRepr sym fm fi
  iFloatLit sym fm fi x = iRealToFloat sym fm fi RNE =<< realLit sym x
  iFloatLitSingle sym fm x =
    iFloatFromBinary sym fm SingleFloatRepr
      =<< (bvLit sym knownNat $ BV.word32 $ IEEE754.floatToWord x)
  iFloatLitDouble sym fm x =
    iFloatFromBinary sym fm DoubleFloatRepr
      =<< (bvLit sym knownNat $ BV.word64 $ IEEE754.doubleToWord x)
  iFloatLitLongDouble sym fm x =
    iFloatFromBinary sym fm X86_80FloatRepr
      =<< (bvLit sym knownNat $ BV.mkBV knownNat $ fp80ToBits x)

  iFloatNeg sym _ = floatUninterpArithUnOp "uninterpreted_float_neg" sym
  iFloatAbs sym _ = floatUninterpArithUnOp "uninterpreted_float_abs" sym
  iFloatSqrt sym _ = floatUninterpArithUnOpR "uninterpreted_float_sqrt" sym
  iFloatAdd sym _ = floatUninterpArithBinOpR "uninterpreted_float_add" sym
  iFloatSub sym _ = floatUninterpArithBinOpR "uninterpreted_float_sub" sym
  iFloatMul sym _ = floatUninterpArithBinOpR "uninterpreted_float_mul" sym
  iFloatDiv sym _ = floatUninterpArithBinOpR "uninterpreted_float_div" sym
  iFloatRem sym _ = floatUninterpArithBinOp "uninterpreted_float_rem" sym
  iFloatMin sym _ = floatUninterpArithBinOp "uninterpreted_float_min" sym
  iFloatMax sym _ = floatUninterpArithBinOp "uninterpreted_float_max" sym
  iFloatFMA sym _ r x y z = do
    let ret_type = exprType x
    r_arg <- roundingModeToSymNat sym r
    mkUninterpFnApp sym
                    "uninterpreted_float_fma"
                    (Ctx.empty Ctx.:> r_arg Ctx.:> x Ctx.:> y Ctx.:> z)
                    ret_type
  iFloatEq sym _ = isEq sym
  iFloatNe sym _ x y = notPred sym =<< isEq sym x y
  iFloatFpEq sym _ = floatUninterpLogicBinOp "uninterpreted_float_fp_eq" sym
  iFloatFpNe sym _ = floatUninterpLogicBinOp "uninterpreted_float_fp_ne" sym
  iFloatLe sym _ = floatUninterpLogicBinOp "uninterpreted_float_le" sym
  iFloatLt sym _ = floatUninterpLogicBinOp "uninterpreted_float_lt" sym
  iFloatGe sym _ x y = floatUninterpLogicBinOp "uninterpreted_float_le" sym y x
  iFloatGt sym _ x y = floatUninterpLogicBinOp "uninterpreted_float_lt" sym y x
  iFloatIte sym _ = baseTypeIte sym
  iFloatIsNaN sym _ = floatUninterpLogicUnOp "uninterpreted_float_is_nan" sym
  iFloatIsInf sym _ = floatUninterpLogicUnOp "uninterpreted_float_is_inf" sym
  iFloatIsZero sym _ = floatUninterpLogicUnOp "uninterpreted_float_is_zero" sym
  iFloatIsPos sym _ = floatUninterpLogicUnOp "uninterpreted_float_is_pos" sym
  iFloatIsNeg sym _ = floatUninterpLogicUnOp "uninterpreted_float_is_neg" sym
  iFloatIsSubnorm sym _ = floatUninterpLogicUnOp "uninterpreted_float_is_subnorm" sym
  iFloatIsNorm sym _ = floatUninterpLogicUnOp "uninterpreted_float_is_norm" sym
  iFloatCast sym fm fi = floatUninterpCastOp "uninterpreted_float_cast" sym $ iFloatBaseTypeRepr sym fm fi
  iFloatRound sym _ = floatUninterpArithUnOpR "uninterpreted_float_round" sym
  iFloatFromBinary _ _ _ = return
  iFloatToBinary _ _ _ = return
  iBVToFloat sym fm =
    floatUninterpCastOp "uninterpreted_bv_to_float" sym . iFloatBaseTypeRepr sym fm
  iSBVToFloat sym fm =
    floatUninterpCastOp "uninterpreted_sbv_to_float" sym . iFloatBaseTypeRepr sym fm
  iRealToFloat sym fm =
    floatUninterpCastOp "uninterpreted_real_to_float" sym . iFloatBaseTypeRepr sym fm
  iFloatToBV sym _ =
    floatUninterpCastOp "uninterpreted_float_to_bv" sym . BaseBVRepr
  iFloatToSBV sym _ =
    floatUninterpCastOp "uninterpreted_float_to_sbv" sym . BaseBVRepr
  iFloatToReal sym _ x =
    mkUninterpFnApp sym
                    "uninterpreted_float_to_real"
                    (Ctx.empty Ctx.:> x)
                    knownRepr
  iFloatBaseTypeRepr _ _ = floatInfoToBVTypeRepr

floatUninterpArithBinOp
  :: IsSymExprBuilder sym => String -> sym -> SymExpr sym bt -> SymExpr sym bt -> IO (SymExpr sym bt)
floatUninterpArithBinOp fn sym x y =
  let ret_type = exprType x
  in  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x Ctx.:> y) ret_type

floatUninterpArithBinOpR
  :: IsSymExprBuilder sym
  => String
  -> sym
  -> RoundingMode
  -> SymExpr sym bt
  -> SymExpr sym bt
  -> IO (SymExpr sym bt)
floatUninterpArithBinOpR fn sym r x y = do
  let ret_type = exprType x
  r_arg <- roundingModeToSymNat sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x Ctx.:> y) ret_type

floatUninterpArithUnOp
  :: IsSymExprBuilder sym => String -> sym -> SymExpr sym bt -> IO (SymExpr sym bt)
floatUninterpArithUnOp fn sym x =
  let ret_type = exprType x
  in  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x) ret_type

floatUninterpArithUnOpR
  :: IsSymExprBuilder sym
  => String
  -> sym
  -> RoundingMode
  -> SymExpr sym bt
  -> IO (SymExpr sym bt)
floatUninterpArithUnOpR fn sym r x = do
  let ret_type = exprType x
  r_arg <- roundingModeToSymNat sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x) ret_type

floatUninterpArithCt
  :: IsSymExprBuilder sym
  => String
  -> sym
  -> BaseTypeRepr bt
  -> IO (SymExpr sym bt)
floatUninterpArithCt fn sym ret_type =
  mkUninterpFnApp sym fn Ctx.empty ret_type

floatUninterpLogicBinOp
  :: IsSymExprBuilder sym
  => String
  -> sym
  -> SymExpr sym bt
  -> SymExpr sym bt
  -> IO (SymExpr sym BaseBoolType)
floatUninterpLogicBinOp fn sym x y =
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x Ctx.:> y) knownRepr

floatUninterpLogicUnOp
  :: IsSymExprBuilder sym
  => String
  -> sym 
  -> SymExpr sym bt
  -> IO (SymExpr sym BaseBoolType)
floatUninterpLogicUnOp fn sym x =
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x) knownRepr

floatUninterpCastOp
  :: IsSymExprBuilder sym
  => String
  -> sym
  -> BaseTypeRepr bt
  -> RoundingMode
  -> SymExpr sym bt'
  -> IO (SymExpr sym bt)
floatUninterpCastOp fn sym ret_type r x = do
  r_arg <- roundingModeToSymNat sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x) ret_type

roundingModeToSymNat
  :: IsExprBuilder sym => sym -> RoundingMode -> IO (SymNat sym)
roundingModeToSymNat sym = natLit sym . fromIntegral . fromEnum


type instance SymInterpretedFloatType FloatIEEE fi = BaseFloatType (FloatInfoToPrecision fi)

instance IsExprBuilder sym => IsInterpretedFloatExprBuilder sym FloatIEEE where
  iFloatPZero sym _ = floatPZero sym . floatInfoToPrecisionRepr
  iFloatNZero sym _ = floatNZero sym . floatInfoToPrecisionRepr
  iFloatNaN sym _ = floatNaN sym . floatInfoToPrecisionRepr
  iFloatPInf sym _ = floatPInf sym . floatInfoToPrecisionRepr
  iFloatNInf sym _ = floatNInf sym . floatInfoToPrecisionRepr
  iFloatLit sym _ = floatLit sym . floatInfoToPrecisionRepr
  iFloatLitSingle sym _ x =
    floatFromBinary sym knownRepr
      =<< (bvLit sym knownNat $ BV.word32 $ IEEE754.floatToWord x)
  iFloatLitDouble sym _ x =
    floatFromBinary sym knownRepr
      =<< (bvLit sym knownNat $ BV.word64 $ IEEE754.doubleToWord x)
  iFloatLitLongDouble sym _ (X86_80Val e s) = do
    el <- bvLit sym (knownNat @16) $ BV.mkBV knownNat $ toInteger e
    sl <- bvLit sym (knownNat @64) $ BV.word64 s
    fl <- bvConcat sym el sl
    floatFromBinary sym knownRepr fl
    -- n.b. This may not be valid semantically for operations
    -- performed on 80-bit values, but it allows them to be present in
    -- formulas.
  iFloatNeg sym _ = floatNeg sym
  iFloatAbs sym _ = floatAbs sym
  iFloatSqrt sym _ = floatSqrt sym
  iFloatAdd sym _ = floatAdd sym
  iFloatSub sym _ = floatSub sym
  iFloatMul sym _ = floatMul sym
  iFloatDiv sym _ = floatDiv sym
  iFloatRem sym _ = floatRem sym
  iFloatMin sym _ = floatMin sym
  iFloatMax sym _ = floatMax sym
  iFloatFMA sym _ = floatFMA sym
  iFloatEq sym _ = floatEq sym
  iFloatNe sym _ = floatNe sym
  iFloatFpEq sym _ = floatFpEq sym
  iFloatFpNe sym _ = floatFpNe sym
  iFloatLe sym _ = floatLe sym
  iFloatLt sym _ = floatLt sym
  iFloatGe sym _ = floatGe sym
  iFloatGt sym _ = floatGt sym
  iFloatIte sym _ = floatIte sym
  iFloatIsNaN sym _ = floatIsNaN sym
  iFloatIsInf sym _ = floatIsInf sym
  iFloatIsZero sym _ = floatIsZero sym
  iFloatIsPos sym _ = floatIsPos sym
  iFloatIsNeg sym _ = floatIsNeg sym
  iFloatIsSubnorm sym _ = floatIsSubnorm sym
  iFloatIsNorm sym _ = floatIsNorm sym
  iFloatCast sym _ = floatCast sym . floatInfoToPrecisionRepr
  iFloatRound sym _ = floatRound sym
  iFloatFromBinary sym _ fi x = case fi of
    HalfFloatRepr         -> floatFromBinary sym knownRepr x
    SingleFloatRepr       -> floatFromBinary sym knownRepr x
    DoubleFloatRepr       -> floatFromBinary sym knownRepr x
    QuadFloatRepr         -> floatFromBinary sym knownRepr x
    X86_80FloatRepr       -> fail "x86_80 is not an IEEE-754 format."
    DoubleDoubleFloatRepr -> fail "double-double is not an IEEE-754 format."
  iFloatToBinary sym _ fi x = case fi of
    HalfFloatRepr         -> floatToBinary sym x
    SingleFloatRepr       -> floatToBinary sym x
    DoubleFloatRepr       -> floatToBinary sym x
    QuadFloatRepr         -> floatToBinary sym x
    X86_80FloatRepr       -> fail "x86_80 is not an IEEE-754 format."
    DoubleDoubleFloatRepr -> fail "double-double is not an IEEE-754 format."
  iBVToFloat sym _ = bvToFloat sym . floatInfoToPrecisionRepr
  iSBVToFloat sym _ = sbvToFloat sym . floatInfoToPrecisionRepr
  iRealToFloat sym _ = realToFloat sym . floatInfoToPrecisionRepr
  iFloatToBV sym _ = floatToBV sym
  iFloatToSBV sym _ = floatToSBV sym
  iFloatToReal sym _ = floatToReal sym
  iFloatBaseTypeRepr _ _ = BaseFloatRepr . floatInfoToPrecisionRepr

instance (IsSymExprBuilder sym, IsInterpretedFloatExprBuilder sym fm) => IsInterpretedFloatSymExprBuilder sym fm
