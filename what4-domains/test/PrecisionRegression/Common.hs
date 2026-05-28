{-
Module      : PrecisionRegression.Common
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Shared infrastructure for the precision regression test:

  * Width-4 enumeration scaffolding ('DomainEnum', 'dedup', 'enumClps4').
  * Concrete-value-set operations on @Natural@ at width 4 (the oracle that
    each abstract op is compared against).
  * Aggregator helpers ('unaryResult', 'binaryResult',
    'binaryResultFiltered', 'scaleResult', 'latticeResult') that turn an
    abstract op + a concrete op into a precision 'Result'.
  * CSV rendering and the per-domain compare/update driver ('runDomain').
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module PrecisionRegression.Common
  ( -- * Width-4 enumeration
    w4
  , mask4
  , DomainEnum(..)
  , dedup
  , enumClps4
    -- * Aggregator
  , Result(..)
  , unaryResult
  , binaryResult
  , binaryResultFiltered
  , scaleResult
  , latticeResult
    -- * Concrete operations
  , cAdd, cSub, cMul, cAnd, cOr, cXor
  , cNegate, cNot, cScale
  , cUdivPartial, cUremPartial, cSdivPartial, cSremPartial
  , cUdivSmtlib, cUremSmtlib, cSdivSmtlib, cSremSmtlib
  , cShl, cLshr, cAshr, cRol, cRor
  , cJoin, cMeet
    -- * Driver
  , runDomain
  ) where

import           Data.Bits ((.&.), shiftL, shiftR)
import qualified Data.Bits as Bits
import           Data.List (sort)
import qualified Data.Set as Set
import           Numeric.Natural (Natural)
import           System.IO (hPutStrLn, stderr)

import           Data.Parameterized.NatRepr (NatRepr, knownNat, maxUnsigned)

import qualified What4.Domains.BV.CLP as C

------------------------------------------------------------------------
-- Width 4

w4 :: NatRepr 4
w4 = knownNat @4

mask4 :: Natural
mask4 = fromInteger (maxUnsigned w4)

------------------------------------------------------------------------
-- Enumerating representatives of a domain at width 4

-- | All distinguishable abstract elements of a domain at width 4, plus the
-- 'toList' projection used to compare value-sets.
data DomainEnum a = DomainEnum
  { deReps   :: ![a]
  , deToList :: !(a -> [Natural])
  }

dedup :: (a -> [Natural]) -> [a] -> [a]
dedup toL = go Set.empty
  where
    go _ [] = []
    go seen (x : xs)
      | Set.member k seen = go seen xs
      | otherwise         = x : go (Set.insert k seen) xs
      where k = sort (toL x)

-- | Enumerate every proper 'C.Clp' at width 4. Reused as the building block
-- for both the CLP and StridedInterval enumerations.
enumClps4 :: [C.Clp 4]
enumClps4 =
  [ C.mk w4 start stride i
  | stride <- [1 .. mask4]
  , let g = stride .&. ((mask4 + 1) - stride)
  , let orbit = (mask4 + 1) `div` g
  , start <- [0 .. mask4]
  , i <- [0 .. orbit - 1]
  ]

------------------------------------------------------------------------
-- Aggregation

data Result = Result
  { resOp   :: !String
  , resAbs  :: !Integer
  , resConc :: !Integer
  }

unaryResult ::
  DomainEnum a ->
  String -> (a -> a) -> (Natural -> Natural) -> Result
unaryResult de name absOp concOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (length (toL (absOp a))) | a <- reps ]
    concTot =
      sum [ fromIntegral (Set.size (Set.fromList (map concOp (toL a))))
          | a <- reps
          ]

binaryResultFiltered ::
  DomainEnum a ->
  String ->
  (a -> a -> a) ->
  (Natural -> Natural -> Maybe Natural) ->
  Result
binaryResultFiltered de name absOp concOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot =
      sum [ fromIntegral (length (toL (absOp a b))) | a <- reps, b <- reps ]
    concTot =
      sum [ fromIntegral (Set.size (Set.fromList
              [ z | x <- toL a, y <- toL b
                  , Just z <- [concOp x y] ]))
          | a <- reps, b <- reps
          ]

binaryResult ::
  DomainEnum a ->
  String ->
  (a -> a -> a) ->
  (Natural -> Natural -> Natural) ->
  Result
binaryResult de name absOp concOp =
  binaryResultFiltered de name absOp (\x y -> Just (concOp x y))

-- | 'scale' takes an Integer constant; aggregate over @k in [0, mask4]@.
scaleResult :: DomainEnum a -> (Integer -> a -> a) -> Result
scaleResult de absOp = Result "scale" absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (length (toL (absOp (toInteger k) a)))
                  | k <- [0 .. mask4], a <- reps ]
    concTot = sum [ fromIntegral (Set.size (Set.fromList
                      [ cScale k x | x <- toL a ]))
                  | k <- [0 .. mask4], a <- reps ]

-- | Aggregator for lattice operations whose oracle is a set operation on
-- the underlying value-sets, rather than a pointwise function.
latticeResult ::
  DomainEnum a ->
  String ->
  (a -> a -> a) ->
  ([Natural] -> [Natural] -> Set.Set Natural) ->
  Result
latticeResult de name absOp concOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (length (toL (absOp a b)))
                  | a <- reps, b <- reps ]
    concTot = sum [ fromIntegral (Set.size (concOp (toL a) (toL b)))
                  | a <- reps, b <- reps ]

------------------------------------------------------------------------
-- Concrete operations

cMask :: Natural -> Natural
cMask x = x .&. mask4

cAdd, cSub, cMul, cAnd, cOr, cXor :: Natural -> Natural -> Natural
cAdd x y = cMask (x + y)
cSub x y = cMask (x + (mask4 + 1 - y))
cMul x y = cMask (x * y)
cAnd x y = x .&. y
cOr  x y = x Bits..|. y
cXor x y = x `Bits.xor` y

cNegate, cNot :: Natural -> Natural
cNegate x = cMask (mask4 + 1 - x)
cNot   x = mask4 `Bits.xor` x

cScale :: Natural -> Natural -> Natural
cScale k x = cMask (k * x)

toSigned4 :: Natural -> Integer
toSigned4 x
  | x .&. 8 == 0 = toInteger x
  | otherwise    = toInteger x - 16

fromSigned4 :: Integer -> Natural
fromSigned4 x = fromInteger (x .&. toInteger mask4)

cUdivPartial, cUremPartial, cSdivPartial, cSremPartial
  :: Natural -> Natural -> Maybe Natural
cUdivPartial _ 0 = Nothing
cUdivPartial x y = Just (x `div` y)
cUremPartial _ 0 = Nothing
cUremPartial x y = Just (x `mod` y)
cSdivPartial _ 0 = Nothing
cSdivPartial x y = Just (fromSigned4 (toSigned4 x `quot` toSigned4 y))
cSremPartial _ 0 = Nothing
cSremPartial x y = Just (fromSigned4 (toSigned4 x `rem` toSigned4 y))

cUdivSmtlib, cUremSmtlib, cSdivSmtlib, cSremSmtlib
  :: Natural -> Natural -> Natural
cUdivSmtlib _ 0 = mask4
cUdivSmtlib x y = x `div` y
cUremSmtlib x 0 = x
cUremSmtlib x y = x `mod` y
cSdivSmtlib x 0
  | toSigned4 x >= 0 = mask4   -- -1
  | otherwise        = 1
cSdivSmtlib x y = fromSigned4 (toSigned4 x `quot` toSigned4 y)
cSremSmtlib x 0 = x
cSremSmtlib x y = fromSigned4 (toSigned4 x `rem` toSigned4 y)

cShl, cLshr, cAshr, cRol, cRor :: Natural -> Natural -> Natural
cShl x y =
  let s = fromIntegral y :: Int
  in if s >= 4 then 0 else cMask (x `shiftL` s)
cLshr x y =
  let s = fromIntegral y :: Int
  in if s >= 4 then 0 else x `shiftR` s
cAshr x y =
  let s = fromIntegral y :: Int
      sx = toSigned4 x
      s' = if s >= 4 then 3 else s
  in fromSigned4 (sx `shiftR` s')
cRol x y =
  let s = fromIntegral (y `mod` 4) :: Int
  in cMask ((x `shiftL` s) Bits..|. (x `shiftR` (4 - s)))
cRor x y =
  let s = fromIntegral (y `mod` 4) :: Int
  in cMask ((x `shiftR` s) Bits..|. (x `shiftL` (4 - s)))

-- | Oracle for lattice 'join': set union of value-sets.
cJoin :: [Natural] -> [Natural] -> Set.Set Natural
cJoin xs ys = Set.fromList xs `Set.union` Set.fromList ys

-- | Oracle for lattice 'meet': set intersection of value-sets.
cMeet :: [Natural] -> [Natural] -> Set.Set Natural
cMeet xs ys = Set.fromList xs `Set.intersection` Set.fromList ys

------------------------------------------------------------------------
-- CSV rendering

renderCsv :: [Result] -> String
renderCsv rs = unlines ("op,abs,conc,precision" : map formatRow rs)

formatRow :: Result -> String
formatRow r =
  resOp r ++ "," ++ show (resAbs r) ++ "," ++ show (resConc r)
    ++ "," ++ formatPercent (resConc r) (resAbs r)

-- | @num \/ denom@ as a percentage to 1 decimal place.
formatPercent :: Integer -> Integer -> String
formatPercent num denom
  | denom == 0 = "0.0%"
  | otherwise =
      let perMille = (num * 1000) `div` denom
          (whole, frac) = perMille `divMod` 10
      in show whole ++ "." ++ show frac ++ "%"

------------------------------------------------------------------------
-- Driver

-- | Compare or refresh one per-domain CSV. Returns 'True' on success.
runDomain :: Bool -> FilePath -> [Result] -> IO Bool
runDomain update path results =
  let actual = renderCsv results in
  if update
    then do
      writeFile path actual
      putStrLn ("Wrote " ++ path)
      pure True
    else do
      expected <- readFile path
      if expected == actual
        then do
          putStrLn ("OK: " ++ path ++ " is up to date")
          pure True
        else do
          hPutStrLn stderr $
            path ++ " is out of date. Expected:\n"
            ++ expected ++ "\nActual:\n" ++ actual
            ++ "\nRun with WHAT4_UPDATE_TEST_EXPECTATIONS=1 to refresh."
          pure False
