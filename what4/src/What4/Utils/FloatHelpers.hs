{-# Language BlockArguments, OverloadedStrings #-}
{-# Language BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# Language GADTs #-}
module What4.Utils.FloatHelpers where

import qualified Control.Exception as Ex
import Data.Ratio(numerator,denominator)
import Data.Hashable
import GHC.Generics (Generic)
import GHC.Stack

import LibBF

import What4.BaseTypes
import What4.Panic (panic)

-- | Rounding modes for IEEE-754 floating point operations.
data RoundingMode
  = RNE -- ^ Round to nearest even.
  | RNA -- ^ Round to nearest away.
  | RTP -- ^ Round toward plus Infinity.
  | RTN -- ^ Round toward minus Infinity.
  | RTZ -- ^ Round toward zero.
  deriving (Eq, Generic, Ord, Show, Enum)

instance Hashable RoundingMode

bfStatus :: HasCallStack => (a, Status) -> a
bfStatus (_, MemError)     = Ex.throw Ex.HeapOverflow
bfStatus (x,_)             = x

fppOpts :: FloatPrecisionRepr fpp -> RoundingMode -> BFOpts
fppOpts (FloatingPointPrecisionRepr eb sb) r =
  fpOpts (intValue eb) (intValue sb) (toRoundMode r)

toRoundMode :: RoundingMode -> RoundMode
toRoundMode RNE = NearEven
toRoundMode RNA = NearAway
toRoundMode RTP = ToPosInf
toRoundMode RTN = ToNegInf
toRoundMode RTZ = ToZero

-- | Make LibBF options for the given precision and rounding mode.
fpOpts :: Integer -> Integer -> RoundMode -> BFOpts
fpOpts e p r =
  case ok of
    Just opts -> opts
    Nothing   -> panic "floatOpts" [ "Invalid Float size"
                                   , "exponent: " ++ show e
                                   , "precision: " ++ show p
                                   ]
  where
  ok = do eb <- rng expBits expBitsMin expBitsMax e
          pb <- rng precBits precBitsMin precBitsMax p
          pure (eb <> pb <> allowSubnormal <> rnd r)

  rng f a b x = if toInteger a <= x && x <= toInteger b
                  then Just (f (fromInteger x))
                  else Nothing


-- | Make a floating point number from an integer, using the given rounding mode
floatFromInteger :: BFOpts -> Integer -> BigFloat
floatFromInteger opts i = bfStatus (bfRoundFloat opts (bfFromInteger i))

-- | Make a floating point number from a rational, using the given rounding mode
floatFromRational :: BFOpts -> Rational -> BigFloat
floatFromRational opts rat = bfStatus
    if den == 1 then bfRoundFloat opts num
                else bfDiv opts num (bfFromInteger den)
  where

  num   = bfFromInteger (numerator rat)
  den   = denominator rat


-- | Convert a floating point number to a rational, if possible.
floatToRational :: BigFloat -> Maybe Rational
floatToRational bf =
  case bfToRep bf of
    BFNaN -> Nothing
    BFRep s num ->
      case num of
        Inf  -> Nothing
        Zero -> Just 0
        Num i ev -> Just case s of
                           Pos -> ab
                           Neg -> negate ab
          where ab = fromInteger i * (2 ^^ ev)

-- | Convert a floating point number to an integer, if possible.
floatToInteger :: RoundingMode -> BigFloat -> Maybe Integer
floatToInteger r fp =
  do rat <- floatToRational fp
     pure case r of
            RNE -> round rat
            RNA -> if rat > 0 then ceiling rat else floor rat
            RTP -> ceiling rat
            RTN -> floor rat
            RTZ -> truncate rat

floatRoundToInt :: HasCallStack =>
  FloatPrecisionRepr fpp -> RoundingMode -> BigFloat -> BigFloat
floatRoundToInt fpp r bf =
  bfStatus (bfRoundFloat (fppOpts fpp r) (bfStatus (bfRoundInt (toRoundMode r) bf)))
