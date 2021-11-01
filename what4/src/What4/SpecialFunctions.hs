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
  ( -- * Representation of special functions
    R
  , SpecialFunction(..)

    -- ** Symmetry properties of special functions
  , FunctionSymmetry(..)
  , specialFnSymmetry

    -- ** Packaging arguments to special functions
  , SpecialFnArg(..)
  , traverseSpecialFnArg
  , SpecialFnArgs(..)
  , traverseSpecialFnArgs

    -- ** Interval data for domain and range
  , RealPoint(..)
  , RealBound(..)
  , RealInterval(..)
  , specialFnDomain
  , specialFnRange
  ) where

import           Data.Kind (Type)
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>) )
import           Data.Parameterized.Ctx
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC

-- | Some special functions exhibit useful symmetries in their arguments.
--   A function @f@ is an odd function if @f(-x) = -f(x)@, and is even
--   if @f(-x) = f(x)@.  We extend this notion to arguments of more than
--   one function by saying that a function is even/odd in its @i@th
--   argument if it is even/odd when the other arguments are fixed.
data FunctionSymmetry r
  = NoSymmetry
  | EvenFunction
  | OddFunction
 deriving (Show)


-- | Phantom data index representing the real number line.
--   Used for specifying the arity of special functions.
data R

-- | Data type for representing \"special\" functions.
--   These include functions from standard and hyperbolic
--   trigonometry, exponential and logarithmic functions,
--   as well as other well-known mathematical functions.
--
--   Generally, little solver support exists for such functions
--   (although systems like dReal and Metatarski can prove some
--   properties).  Nonetheless, we may have some information about
--   specific values these functions take, the domains on which they
--   are defined, or the range of values their outputs may take, or
--   specific relationships that may exists between these functions
--   (e.g., trig identities).  This information may, in some
--   circumstances, be sufficent to prove properties of interest, even
--   if the functions cannot be represented in their entirety.
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

  -- exponential and logarithm functions
  Pow     :: SpecialFunction (EmptyCtx ::> R ::> R) -- x^y
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

  -- lossy conversions
  Ceiling :: SpecialFunction (EmptyCtx ::> R) -- ceil(x)
  Floor   :: SpecialFunction (EmptyCtx ::> R) -- floor(x)

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

    Pow            -> "pow"
    Exp            -> "exp"
    Log            -> "ln"
    Expm1          -> "expm1"
    Log1p          -> "log1p"
    Exp2           -> "exp2"
    Log2           -> "log2"
    Exp10          -> "exp10"
    Log10          -> "log10"

    Ceiling        -> "ceiling"
    Floor          -> "floor"

-- | Values that can appear in the definition of domain and
--   range intervals for special functions.
data RealPoint
  = Zero
  | NegOne
  | PosOne
  | NegInf
  | PosInf
  | NegPi
  | PosPi
  | NegHalfPi
  | PosHalfPi

instance Show RealPoint where
  show Zero   = "0"
  show NegOne = "-1"
  show PosOne = "+1"
  show NegInf = "-∞"
  show PosInf = "+∞"
  show NegPi  = "-π"
  show PosPi  = "+π"
  show NegHalfPi = "-π/2"
  show PosHalfPi = "+π/2"

-- | The endpoint of an interval, which may be inclusive or exclusive.
data RealBound
  = Incl RealPoint
  | Excl RealPoint

-- | An interval on real values, or a point.
data RealInterval r where
  RealPoint    :: SpecialFunction EmptyCtx -> RealInterval R
  RealInterval :: RealBound -> RealBound -> RealInterval R

instance Show (RealInterval r) where
  show (RealPoint x) = show x
  show (RealInterval lo hi) = lostr ++ ", " ++ histr
    where
      lostr = case lo of
                Incl x -> "[" ++ show x
                Excl x -> "(" ++ show x
      histr = case hi of
                Incl x -> show x ++ "]"
                Excl x -> show x ++ ")"

-- | Compute function symmetry information for the given special function.
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
    Arccosh        -> Ctx.Empty :> NoSymmetry
    Arctanh        -> Ctx.Empty :> OddFunction

    Pow            -> Ctx.Empty :> NoSymmetry :> NoSymmetry
    Exp            -> Ctx.Empty :> NoSymmetry
    Log            -> Ctx.Empty :> NoSymmetry
    Expm1          -> Ctx.Empty :> NoSymmetry
    Log1p          -> Ctx.Empty :> NoSymmetry
    Exp2           -> Ctx.Empty :> NoSymmetry
    Log2           -> Ctx.Empty :> NoSymmetry
    Exp10          -> Ctx.Empty :> NoSymmetry
    Log10          -> Ctx.Empty :> NoSymmetry

    Hypot          -> Ctx.Empty :> EvenFunction :> EvenFunction
    Arctan2        -> Ctx.Empty :> OddFunction :> NoSymmetry

    Ceiling        -> Ctx.Empty :> NoSymmetry
    Floor          -> Ctx.Empty :> NoSymmetry


-- | Compute the range of values that may be returned by the given special function
--   as its arguments take on the possible values of its domain.  This may include
--   limiting values if the function's domain includes infinities; for example
--   @exp(-inf) = 0@.
specialFnRange :: SpecialFunction args -> RealInterval R
specialFnRange fn = case fn of
    Pi             -> RealPoint Pi
    HalfPi         -> RealPoint HalfPi
    QuarterPi      -> RealPoint QuarterPi
    OneOverPi      -> RealPoint OneOverPi
    TwoOverPi      -> RealPoint TwoOverPi
    TwoOverSqrt_Pi -> RealPoint TwoOverSqrt_Pi
    Sqrt_2         -> RealPoint Sqrt_2
    Sqrt_OneHalf   -> RealPoint Sqrt_OneHalf
    E              -> RealPoint E
    Log2_E         -> RealPoint Log2_E
    Log10_E        -> RealPoint Log10_E
    Ln_2           -> RealPoint Ln_2
    Ln_10          -> RealPoint Ln_10

    Sin            -> RealInterval (Incl NegOne) (Incl PosOne)
    Cos            -> RealInterval (Incl NegOne) (Incl PosOne)
    Tan            -> RealInterval (Incl NegInf) (Incl PosInf)

    Arcsin         -> RealInterval (Incl NegHalfPi) (Incl PosHalfPi)
    Arccos         -> RealInterval (Incl Zero)      (Incl PosPi)
    Arctan         -> RealInterval (Incl NegHalfPi) (Incl PosHalfPi)

    Sinh           -> RealInterval (Incl NegInf) (Incl PosInf)
    Cosh           -> RealInterval (Incl PosOne) (Incl PosInf)
    Tanh           -> RealInterval (Incl NegOne) (Incl PosOne)
    Arcsinh        -> RealInterval (Incl NegInf) (Incl PosInf)
    Arccosh        -> RealInterval (Incl Zero)   (Incl PosInf)
    Arctanh        -> RealInterval (Incl NegInf) (Incl PosInf)

    Pow            -> RealInterval (Incl NegInf) (Incl PosInf)
    Exp            -> RealInterval (Incl Zero)   (Incl PosInf)
    Log            -> RealInterval (Incl NegInf) (Incl PosInf)
    Expm1          -> RealInterval (Incl NegOne) (Incl PosInf)
    Log1p          -> RealInterval (Incl NegInf) (Incl PosInf)
    Exp2           -> RealInterval (Incl Zero)   (Incl PosInf)
    Log2           -> RealInterval (Incl NegInf) (Incl PosInf)
    Exp10          -> RealInterval (Incl Zero)   (Incl PosInf)
    Log10          -> RealInterval (Incl NegInf) (Incl PosInf)

    Hypot          -> RealInterval (Incl Zero) (Incl PosInf)
    Arctan2        -> RealInterval (Incl NegPi) (Incl PosPi)

    Ceiling        -> RealInterval (Incl NegInf) (Incl PosInf)
    Floor          -> RealInterval (Incl NegInf) (Incl PosInf)


-- | Compute the domain of the given special function.  As a mathematical
--   entity, the value of the given function is not well-defined outside
--   its domain. In floating-point terms, a special function will return
--   a @NaN@ when evaluated on arguments outside its domain.
specialFnDomain :: SpecialFunction args -> Ctx.Assignment RealInterval args
specialFnDomain fn = case fn of
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

    Sin            -> Ctx.Empty :> RealInterval (Excl NegInf) (Excl PosInf)
    Cos            -> Ctx.Empty :> RealInterval (Excl NegInf) (Excl PosInf)
    Tan            -> Ctx.Empty :> RealInterval (Excl NegInf) (Excl PosInf)
    Arcsin         -> Ctx.Empty :> RealInterval (Incl NegOne) (Incl PosOne)
    Arccos         -> Ctx.Empty :> RealInterval (Incl NegOne) (Incl PosOne)
    Arctan         -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)

    Sinh           -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Cosh           -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Tanh           -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Arcsinh        -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Arccosh        -> Ctx.Empty :> RealInterval (Incl PosOne) (Incl PosInf)
    Arctanh        -> Ctx.Empty :> RealInterval (Incl NegOne) (Incl PosOne)

    Pow            -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
                                :> RealInterval (Incl NegInf) (Incl PosInf)
    Exp            -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Log            -> Ctx.Empty :> RealInterval (Incl Zero)   (Incl PosInf)
    Expm1          -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Log1p          -> Ctx.Empty :> RealInterval (Incl NegOne) (Incl PosInf)
    Exp2           -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Log2           -> Ctx.Empty :> RealInterval (Incl Zero)   (Incl PosInf)
    Exp10          -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Log10          -> Ctx.Empty :> RealInterval (Incl Zero)   (Incl PosInf)

    Hypot          -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
                                :> RealInterval (Incl NegInf) (Incl PosInf)
    Arctan2        -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
                                :> RealInterval (Incl NegInf) (Incl PosInf)

    Ceiling        -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)
    Floor          -> Ctx.Empty :> RealInterval (Incl NegInf) (Incl PosInf)

-- | Data type for wrapping the actual arguments to special functions.
data SpecialFnArg (e :: k -> Type) (tp::k) (r::Type) where
  SpecialFnArg :: e tp -> SpecialFnArg e tp R

-- | Data type for wrapping a collction of actual arguments to special functions.
newtype SpecialFnArgs (e :: k -> Type) (tp :: k) args =
  SpecialFnArgs (Ctx.Assignment (SpecialFnArg e tp) args)

$(return [])

instance HashableF SpecialFunction where
  hashWithSaltF = $(structuralHashWithSalt [t|SpecialFunction|] [])

instance Hashable (SpecialFunction args) where
  hashWithSalt = hashWithSaltF

instance TestEquality SpecialFunction where
  testEquality = $(structuralTypeEquality [t|SpecialFunction|] [])

instance OrdF SpecialFunction where
  compareF = $(structuralTypeOrd [t|SpecialFunction|] [])


instance OrdF e => TestEquality (SpecialFnArg e tp) where
  testEquality (SpecialFnArg x) (SpecialFnArg y) =
    do Refl <- testEquality x y
       return Refl

instance OrdF e => OrdF (SpecialFnArg e tp) where
  compareF (SpecialFnArg x) (SpecialFnArg y) =
    case compareF x y of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF

instance HashableF e => HashableF (SpecialFnArg e tp) where
  hashWithSaltF s (SpecialFnArg x) = hashWithSaltF s x


instance OrdF e => Eq (SpecialFnArgs e tp r) where
  SpecialFnArgs xs == SpecialFnArgs ys = xs == ys

instance OrdF e => Ord (SpecialFnArgs e tp r) where
  compare (SpecialFnArgs xs) (SpecialFnArgs ys) = compare xs ys

instance HashableF e => Hashable (SpecialFnArgs e tp args) where
  hashWithSalt s (SpecialFnArgs xs) = hashWithSaltF s xs


traverseSpecialFnArg :: Applicative m =>
  (e tp -> m (f tp)) ->
  SpecialFnArg e tp r -> m (SpecialFnArg f tp r)
traverseSpecialFnArg f (SpecialFnArg x) = SpecialFnArg <$> f x

traverseSpecialFnArgs :: Applicative m =>
  (e tp -> m (f tp)) ->
  SpecialFnArgs e tp r -> m (SpecialFnArgs f tp r)
traverseSpecialFnArgs f (SpecialFnArgs xs) =
  SpecialFnArgs <$> traverseFC (traverseSpecialFnArg f) xs
