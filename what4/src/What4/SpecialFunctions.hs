{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  ( SpecialFunction(..)
  , specialFnArgs
  , FunctionSymmetry(..)
  , specialFnSymmetry
  ) where

import Data.Parameterized.Ctx
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Context ( pattern (:>) )

data FunctionSymmetry r
  = NoSymmetry
  | EvenFunction
  | OddFunction
 deriving (Show)

-- | Data type for representing
data SpecialFunction (r :: domain) (args :: Ctx domain) where
  -- constant values involving Pi
  Pi       :: SpecialFunction r EmptyCtx -- pi
  Pi_2     :: SpecialFunction r EmptyCtx -- pi/2
  Pi_4     :: SpecialFunction r EmptyCtx -- pi/4
  PiUnder1 :: SpecialFunction r EmptyCtx -- 1/pi
  PiUnder2 :: SpecialFunction r EmptyCtx -- 2/pi
  SqrtPiUnder2 :: SpecialFunction r EmptyCtx -- 2/sqrt(pi)

  -- constant root values
  Sqrt2    :: SpecialFunction r EmptyCtx -- sqrt(2)
  Sqrt1_2  :: SpecialFunction r EmptyCtx -- sqrt(1/2)

  -- constant values involving exponentials and logarithms
  E       :: SpecialFunction r EmptyCtx  -- e = exp(1)
  Log_2E  :: SpecialFunction r EmptyCtx  -- log_2(e)
  Log_10E :: SpecialFunction r EmptyCtx  -- log_10(e)
  Ln2     :: SpecialFunction r EmptyCtx  -- ln(2)
  Ln10    :: SpecialFunction r EmptyCtx  -- ln(10)

  -- circular trigonometry functions
  Sin    :: SpecialFunction r (EmptyCtx ::> r) -- sin(x)
  Cos    :: SpecialFunction r (EmptyCtx ::> r) -- cos(x)
  Tan    :: SpecialFunction r (EmptyCtx ::> r) -- tan(x) = sin(x)/cos(x)
  Arcsin :: SpecialFunction r (EmptyCtx ::> r) -- inverse sin
  Arccos :: SpecialFunction r (EmptyCtx ::> r) -- inverse cos
  Arctan :: SpecialFunction r (EmptyCtx ::> r) -- inverse tan

  -- hyperbolic trigonometry functions
  Sinh    :: SpecialFunction r (EmptyCtx ::> r) -- sinh(x) (hyperbolic sine)
  Cosh    :: SpecialFunction r (EmptyCtx ::> r) -- cosh(x)
  Tanh    :: SpecialFunction r (EmptyCtx ::> r) -- tanh(x)
  Arcsinh :: SpecialFunction r (EmptyCtx ::> r) -- inverse sinh
  Arccosh :: SpecialFunction r (EmptyCtx ::> r) -- inverse cosh
  Arctanh :: SpecialFunction r (EmptyCtx ::> r) -- inverse tanh

  -- rectangular to polar coordinate conversion
  Hypot   :: SpecialFunction r (EmptyCtx ::> r ::> r) -- hypot(x,y) = sqrt(x^2 + y^2)
  Arctan2 :: SpecialFunction r (EmptyCtx ::> r ::> r) -- atan2(y,x) = atan(y/x)

  -- natural exponential and logarithm
  Exp     :: SpecialFunction r (EmptyCtx ::> r) -- exp(x)
  Log     :: SpecialFunction r (EmptyCtx ::> r) -- ln(x)
  Expm1   :: SpecialFunction r (EmptyCtx ::> r) -- exp(x) - 1
  Log1p   :: SpecialFunction r (EmptyCtx ::> r) -- ln(1+x)

  -- base 2 exponential and logarithm
  Exp_2   :: SpecialFunction r (EmptyCtx ::> r) -- 2^x
  Log_2   :: SpecialFunction r (EmptyCtx ::> r) -- log_2(x)

  -- base 10 exponential and logarithm
  Exp_10  :: SpecialFunction r (EmptyCtx ::> r) -- 10^x
  Log_10  :: SpecialFunction r (EmptyCtx ::> r) -- log_10(x)

instance Show (SpecialFunction r args) where
  show fn = case fn of
    Pi           -> "π"
    Pi_2         -> "π/2"
    Pi_4         -> "π/4"
    PiUnder1     -> "1/π"
    PiUnder2     -> "2/π"
    SqrtPiUnder2 -> "2/sqrt(π)"
    Sqrt2        -> "sqrt(2)"
    Sqrt1_2      -> "sqrt(1/2)"

    E            -> "e"
    Log_2E       -> "log₂(e)"
    Log_10E      -> "log₁₀(e)"
    Ln2          -> "ln(2)"
    Ln10         -> "ln(10)"

    Sin          -> "sin"
    Cos          -> "cos"
    Tan          -> "tan"
    Arcsin       -> "arcsin"
    Arccos       -> "arccos"
    Arctan       -> "arctan"

    Sinh         -> "sinh"
    Cosh         -> "cosh"
    Tanh         -> "tanh"
    Arcsinh      -> "arcsinh"
    Arccosh      -> "arccosh"
    Arctanh      -> "arctanh"

    Hypot        -> "hypot"
    Arctan2      -> "atan2"

    Exp          -> "exp"
    Log          -> "ln"
    Expm1        -> "expm1"
    Log1p        -> "log1p"
    Exp_2        -> "exp₂"
    Log_2        -> "log₂"
    Exp_10       -> "exp₁₀"
    Log_10       -> "log₁₀"

specialFnSymmetry :: SpecialFunction r args -> Ctx.Assignment FunctionSymmetry args
specialFnSymmetry fn = case fn of
    Pi           -> Ctx.Empty
    Pi_2         -> Ctx.Empty
    Pi_4         -> Ctx.Empty
    PiUnder1     -> Ctx.Empty
    PiUnder2     -> Ctx.Empty
    SqrtPiUnder2 -> Ctx.Empty
    Sqrt2        -> Ctx.Empty
    Sqrt1_2      -> Ctx.Empty

    E            -> Ctx.Empty
    Log_2E       -> Ctx.Empty
    Log_10E      -> Ctx.Empty
    Ln2          -> Ctx.Empty
    Ln10         -> Ctx.Empty

    Sin          -> Ctx.Empty :> OddFunction
    Cos          -> Ctx.Empty :> EvenFunction
    Tan          -> Ctx.Empty :> OddFunction
    Arcsin       -> Ctx.Empty :> OddFunction
    Arccos       -> Ctx.Empty :> NoSymmetry
    Arctan       -> Ctx.Empty :> OddFunction

    Sinh         -> Ctx.Empty :> OddFunction
    Cosh         -> Ctx.Empty :> EvenFunction
    Tanh         -> Ctx.Empty :> OddFunction
    Arcsinh      -> Ctx.Empty :> OddFunction
    Arccosh      -> Ctx.Empty :> NoSymmetry -- TODO? is it actually even?
    Arctanh      -> Ctx.Empty :> OddFunction

    Exp          -> Ctx.Empty :> NoSymmetry
    Log          -> Ctx.Empty :> NoSymmetry
    Expm1        -> Ctx.Empty :> NoSymmetry
    Log1p        -> Ctx.Empty :> NoSymmetry
    Exp_2        -> Ctx.Empty :> NoSymmetry
    Log_2        -> Ctx.Empty :> NoSymmetry
    Exp_10       -> Ctx.Empty :> NoSymmetry
    Log_10       -> Ctx.Empty :> NoSymmetry

    Hypot        -> Ctx.Empty :> NoSymmetry :> NoSymmetry
    Arctan2      -> Ctx.Empty :> NoSymmetry :> NoSymmetry -- TODO? is it actually odd in both arguments?


specialFnArgs :: f r -> SpecialFunction r args -> Ctx.Assignment f args
specialFnArgs repr fn = case fn of
    Pi           -> Ctx.Empty
    Pi_2         -> Ctx.Empty
    Pi_4         -> Ctx.Empty
    PiUnder1     -> Ctx.Empty
    PiUnder2     -> Ctx.Empty
    SqrtPiUnder2 -> Ctx.Empty
    Sqrt2        -> Ctx.Empty
    Sqrt1_2      -> Ctx.Empty

    E            -> Ctx.Empty
    Log_2E       -> Ctx.Empty
    Log_10E      -> Ctx.Empty
    Ln2          -> Ctx.Empty
    Ln10         -> Ctx.Empty

    Sin          -> Ctx.Empty :> repr
    Cos          -> Ctx.Empty :> repr
    Tan          -> Ctx.Empty :> repr
    Arcsin       -> Ctx.Empty :> repr
    Arccos       -> Ctx.Empty :> repr
    Arctan       -> Ctx.Empty :> repr

    Sinh         -> Ctx.Empty :> repr
    Cosh         -> Ctx.Empty :> repr
    Tanh         -> Ctx.Empty :> repr
    Arcsinh      -> Ctx.Empty :> repr
    Arccosh      -> Ctx.Empty :> repr
    Arctanh      -> Ctx.Empty :> repr

    Exp          -> Ctx.Empty :> repr
    Log          -> Ctx.Empty :> repr
    Expm1        -> Ctx.Empty :> repr
    Log1p        -> Ctx.Empty :> repr
    Exp_2        -> Ctx.Empty :> repr
    Log_2        -> Ctx.Empty :> repr
    Exp_10       -> Ctx.Empty :> repr
    Log_10       -> Ctx.Empty :> repr

    Hypot        -> Ctx.Empty :> repr :> repr
    Arctan2      -> Ctx.Empty :> repr :> repr
