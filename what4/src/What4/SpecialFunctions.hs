{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module           : What4.SpecialFunctions
Description      : Utilities relating to special functions
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>

Utilties for representing and handling certain \"special\"
functions arising from analysis. Although many of these
functions are most properly understood as complex valued
functions on complex arguments, here we are primarily interested
in their restriction to real-valued functions or their
floating-point approximations.

The functions considered here include functions from
standard and hyperbolic trigonometry, exponential
and logarithmic functions, etc.  Some of these functions
are defineable in terms of others (e.g. @tan(x) = sin(x)/cos(x)@
or expm1(x) = exp(x) - 1@) but are commonly implemented
separately in math libraries for increased precision.
Some popular constant values are also included.
-}

module What4.SpecialFunctions
  ( R
  , SpecialFunction(..)
  , buildSpecialFnArgs
  , FunctionSymmetry(..)
  , specialFnSymmetry
  , SpecialFnArg(..)
  , traverseSpecialFnArg
  , SpecialFnArgs(..)
  , traverseSpecialFnArgs
  ) where

import           Data.Kind (Type)
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>) )
import           Data.Parameterized.Ctx
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC

data FunctionSymmetry r
  = NoSymmetry
  | EvenFunction
  | OddFunction
 deriving (Show)

data R

-- | Data type for representing
data SpecialFunction (args :: Ctx Type) where
  -- constant values involving Pi
  Pi             :: SpecialFunction EmptyCtx -- pi
  HalfPi         :: SpecialFunction EmptyCtx -- pi/2
  QuarterPi      :: SpecialFunction EmptyCtx -- pi/4
  OneOverPi      :: SpecialFunction EmptyCtx -- 1/pi
  TwoOverPi      :: SpecialFunction EmptyCtx -- 2/pi
  TwoOverSqrt_Pi :: SpecialFunction EmptyCtx -- 2/sqrt(pi)

  -- constant root values
  Sqrt_2         :: SpecialFunction EmptyCtx -- sqrt(2)
  Sqrt_OneHalf   :: SpecialFunction EmptyCtx -- sqrt(1/2)

  -- constant values involving exponentials and logarithms
  E              :: SpecialFunction EmptyCtx  -- e = exp(1)
  Log2_E         :: SpecialFunction EmptyCtx  -- log_2(e)
  Log10_E        :: SpecialFunction EmptyCtx  -- log_10(e)
  Ln_2           :: SpecialFunction EmptyCtx  -- ln(2)
  Ln_10          :: SpecialFunction EmptyCtx  -- ln(10)

  -- circular trigonometry functions
  Sin    :: SpecialFunction (EmptyCtx ::> R) -- sin(x)
  Cos    :: SpecialFunction (EmptyCtx ::> R) -- cos(x)
  Tan    :: SpecialFunction (EmptyCtx ::> R) -- tan(x) = sin(x)/cos(x)
  Arcsin :: SpecialFunction (EmptyCtx ::> R) -- inverse sin
  Arccos :: SpecialFunction (EmptyCtx ::> R) -- inverse cos
  Arctan :: SpecialFunction (EmptyCtx ::> R) -- inverse tan

  -- hyperbolic trigonometry functions
  Sinh    :: SpecialFunction (EmptyCtx ::> R) -- sinh(x) (hyperbolic sine)
  Cosh    :: SpecialFunction (EmptyCtx ::> R) -- cosh(x)
  Tanh    :: SpecialFunction (EmptyCtx ::> R) -- tanh(x)
  Arcsinh :: SpecialFunction (EmptyCtx ::> R) -- inverse sinh
  Arccosh :: SpecialFunction (EmptyCtx ::> R) -- inverse cosh
  Arctanh :: SpecialFunction (EmptyCtx ::> R) -- inverse tanh

  -- rectangular to polar coordinate conversion
  Hypot   :: SpecialFunction (EmptyCtx ::> R ::> R) -- hypot(x,y) = sqrt(x^2 + y^2)
  Arctan2 :: SpecialFunction (EmptyCtx ::> R ::> R) -- atan2(y,x) = atan(y/x)

  -- natural exponential and logarithm
  Exp     :: SpecialFunction (EmptyCtx ::> R) -- exp(x)
  Log     :: SpecialFunction (EmptyCtx ::> R) -- ln(x)
  Expm1   :: SpecialFunction (EmptyCtx ::> R) -- exp(x) - 1
  Log1p   :: SpecialFunction (EmptyCtx ::> R) -- ln(1+x)

  -- base 2 exponential and logarithm
  Exp2    :: SpecialFunction (EmptyCtx ::> R) -- 2^x
  Log2    :: SpecialFunction (EmptyCtx ::> R) -- log_2(x)

  -- base 10 exponential and logarithm
  Exp10   :: SpecialFunction (EmptyCtx ::> R) -- 10^x
  Log10   :: SpecialFunction (EmptyCtx ::> R) -- log_10(x)

instance Show (SpecialFunction args) where
  show fn = case fn of
    Pi             -> "pi"
    HalfPi         -> "halfPi"
    QuarterPi      -> "quaterPi"
    OneOverPi      -> "oneOverPi"
    TwoOverPi      -> "twoOverPi"
    TwoOverSqrt_Pi -> "twoOverSqrt_Pi"
    Sqrt_2         -> "sqrt_2"
    Sqrt_OneHalf   -> "sqrt_oneHalf"

    E              -> "e"
    Log2_E         -> "log2_e"
    Log10_E        -> "log10_e"
    Ln_2           -> "ln_2"
    Ln_10          -> "ln_10"

    Sin            -> "sin"
    Cos            -> "cos"
    Tan            -> "tan"
    Arcsin         -> "arcsin"
    Arccos         -> "arccos"
    Arctan         -> "arctan"

    Sinh           -> "sinh"
    Cosh           -> "cosh"
    Tanh           -> "tanh"
    Arcsinh        -> "arcsinh"
    Arccosh        -> "arccosh"
    Arctanh        -> "arctanh"

    Hypot          -> "hypot"
    Arctan2        -> "atan2"

    Exp            -> "exp"
    Log            -> "ln"
    Expm1          -> "expm1"
    Log1p          -> "log1p"
    Exp2           -> "exp2"
    Log2           -> "log2"
    Exp10          -> "exp10"
    Log10          -> "log10"

specialFnSymmetry :: SpecialFunction args -> Ctx.Assignment FunctionSymmetry args
specialFnSymmetry fn = case fn of
    Pi             -> Ctx.Empty
    HalfPi         -> Ctx.Empty
    QuarterPi      -> Ctx.Empty
    OneOverPi      -> Ctx.Empty
    TwoOverPi      -> Ctx.Empty
    TwoOverSqrt_Pi -> Ctx.Empty
    Sqrt_2         -> Ctx.Empty
    Sqrt_OneHalf   -> Ctx.Empty
    E              -> Ctx.Empty
    Log2_E         -> Ctx.Empty
    Log10_E        -> Ctx.Empty
    Ln_2           -> Ctx.Empty
    Ln_10          -> Ctx.Empty

    Sin            -> Ctx.Empty :> OddFunction
    Cos            -> Ctx.Empty :> EvenFunction
    Tan            -> Ctx.Empty :> OddFunction
    Arcsin         -> Ctx.Empty :> OddFunction
    Arccos         -> Ctx.Empty :> NoSymmetry
    Arctan         -> Ctx.Empty :> OddFunction

    Sinh           -> Ctx.Empty :> OddFunction
    Cosh           -> Ctx.Empty :> EvenFunction
    Tanh           -> Ctx.Empty :> OddFunction
    Arcsinh        -> Ctx.Empty :> OddFunction
    Arccosh        -> Ctx.Empty :> NoSymmetry -- TODO? is it actually even?
    Arctanh        -> Ctx.Empty :> OddFunction

    Exp            -> Ctx.Empty :> NoSymmetry
    Log            -> Ctx.Empty :> NoSymmetry
    Expm1          -> Ctx.Empty :> NoSymmetry
    Log1p          -> Ctx.Empty :> NoSymmetry
    Exp2           -> Ctx.Empty :> NoSymmetry
    Log2           -> Ctx.Empty :> NoSymmetry
    Exp10          -> Ctx.Empty :> NoSymmetry
    Log10          -> Ctx.Empty :> NoSymmetry

    Hypot          -> Ctx.Empty :> NoSymmetry :> NoSymmetry
    Arctan2        -> Ctx.Empty :> NoSymmetry :> NoSymmetry -- TODO? is it actually odd in both arguments?


buildSpecialFnArgs :: f R -> SpecialFunction args -> Ctx.Assignment f args
buildSpecialFnArgs repr fn = case fn of
    Pi             -> Ctx.Empty
    HalfPi         -> Ctx.Empty
    QuarterPi      -> Ctx.Empty
    OneOverPi      -> Ctx.Empty
    TwoOverPi      -> Ctx.Empty
    TwoOverSqrt_Pi -> Ctx.Empty
    Sqrt_2         -> Ctx.Empty
    Sqrt_OneHalf   -> Ctx.Empty
    E              -> Ctx.Empty
    Log2_E         -> Ctx.Empty
    Log10_E        -> Ctx.Empty
    Ln_2           -> Ctx.Empty
    Ln_10          -> Ctx.Empty

    Sin            -> Ctx.Empty :> repr
    Cos            -> Ctx.Empty :> repr
    Tan            -> Ctx.Empty :> repr
    Arcsin         -> Ctx.Empty :> repr
    Arccos         -> Ctx.Empty :> repr
    Arctan         -> Ctx.Empty :> repr

    Sinh           -> Ctx.Empty :> repr
    Cosh           -> Ctx.Empty :> repr
    Tanh           -> Ctx.Empty :> repr
    Arcsinh        -> Ctx.Empty :> repr
    Arccosh        -> Ctx.Empty :> repr
    Arctanh        -> Ctx.Empty :> repr

    Exp            -> Ctx.Empty :> repr
    Log            -> Ctx.Empty :> repr
    Expm1          -> Ctx.Empty :> repr
    Log1p          -> Ctx.Empty :> repr
    Exp2           -> Ctx.Empty :> repr
    Log2           -> Ctx.Empty :> repr
    Exp10          -> Ctx.Empty :> repr
    Log10          -> Ctx.Empty :> repr

    Hypot          -> Ctx.Empty :> repr :> repr
    Arctan2        -> Ctx.Empty :> repr :> repr


data SpecialFnArg (e :: k -> Type) (tp::k) (r::Type) where
  SpecialFnArg :: e tp -> SpecialFnArg e tp R

newtype SpecialFnArgs (e :: k -> Type) (tp :: k) args =
  SpecialFnArgs (Ctx.Assignment (SpecialFnArg e tp) args)

$(return [])

instance HashableF SpecialFunction where
  hashWithSaltF = $(structuralHashWithSalt [t|SpecialFunction|] [])

instance Hashable (SpecialFunction args) where
  hashWithSalt = hashWithSaltF

instance TestEquality SpecialFunction where
  testEquality = $(structuralTypeEquality [t|SpecialFunction|] [])

instance OrdF e => TestEquality (SpecialFnArg e tp) where
  testEquality (SpecialFnArg x) (SpecialFnArg y) =
    do Refl <- testEquality x y
       return Refl

instance HashableF e => HashableF (SpecialFnArg e tp) where
  hashWithSaltF s (SpecialFnArg x) = hashWithSaltF s x

traverseSpecialFnArg :: Applicative m =>
  (e tp -> m (f tp)) ->
  SpecialFnArg e tp r -> m (SpecialFnArg f tp r)
traverseSpecialFnArg f (SpecialFnArg x) = SpecialFnArg <$> f x

instance OrdF e => Eq (SpecialFnArgs e tp r) where
  SpecialFnArgs xs == SpecialFnArgs ys = xs == ys

instance HashableF e => Hashable (SpecialFnArgs e tp args) where
  hashWithSalt s (SpecialFnArgs xs) = hashWithSaltF s xs

traverseSpecialFnArgs :: Applicative m =>
  (e tp -> m (f tp)) ->
  SpecialFnArgs e tp r -> m (SpecialFnArgs f tp r)
traverseSpecialFnArgs f (SpecialFnArgs xs) =
  SpecialFnArgs <$> traverseFC (traverseSpecialFnArg f) xs
