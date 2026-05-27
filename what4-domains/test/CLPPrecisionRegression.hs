{-
Module      : CLPPrecisionRegression
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Exhaustive precision regression for CLP operations at width 4.

For each operation @f@ on 'Clp':

  * Enumerate all proper CLPs at width 4 and deduplicate by underlying
    value-set. Call the result @reps@.

  * For unary ops, for each @a in reps@: let @|abs|  = |toList (f a)|@ and
    @|conc| = |{ f x | x in toList a }|@.

  * For binary ops, do the analogous cross-product over @reps^2@. For ops
    that are partial on a divisor of zero (udiv, urem, sdiv, srem) pairs
    with @y = 0@ are skipped on the concrete side.

The aggregate (op, |abs|, |conc|, %) is written to
@test\/CLP\/precision.csv@. By default the test asserts the actual numbers
match the recorded ones; setting @WHAT4_UPDATE_TEST_EXPECTATIONS=1@ writes
a new CSV instead. The percentage column is @|conc| \/ |abs|@ to one
decimal place; higher is more precise.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import           Data.Bits ((.&.), shiftL, shiftR)
import qualified Data.Bits as Bits
import           Data.List (sort)
import qualified Data.Set as Set
import           Numeric.Natural (Natural)
import           System.Environment (lookupEnv)
import           System.Exit (exitFailure, exitSuccess)
import           System.IO (hPutStrLn, stderr)

import           Data.Parameterized.NatRepr (NatRepr, knownNat, maxUnsigned)

import qualified What4.Domains.BV.CLP as C

------------------------------------------------------------------------
-- Width 4

w4 :: NatRepr 4
w4 = knownNat @4

mask4 :: Natural
mask4 = fromInteger (maxUnsigned w4)

-- | Enumerate every proper 'C.Clp' at width 4.
enumClps4 :: [C.Clp 4]
enumClps4 =
  [ C.mk w4 start end stride
  | stride <- [1 .. mask4]
  , let g = stride .&. ((mask4 + 1) - stride)
  , let orbit = (mask4 + 1) `div` g
  , start <- [0 .. mask4]
  , i <- [0 .. orbit - 1]
  , let end = (start + i * stride) .&. mask4
  ]

-- | One representative per distinct value-set.
reps4 :: [C.Clp 4]
reps4 = uniq Set.empty (map (\c -> (sort (C.toList c), c)) enumClps4)
  where
    uniq _ [] = []
    uniq seen ((k, c) : rest)
      | Set.member k seen = uniq seen rest
      | otherwise         = c : uniq (Set.insert k seen) rest

------------------------------------------------------------------------
-- Aggregation

data Result = Result
  { resOp   :: !String
  , resAbs  :: !Integer
  , resConc :: !Integer
  }

absSetSize :: C.Clp w -> Integer
absSetSize c = fromIntegral (length (C.toList c))

unaryResult ::
  String -> (C.Clp 4 -> C.Clp 4) -> (Natural -> Natural) -> Result
unaryResult name absOp concOp = Result name absTot concTot
  where
    absTot  = sum [ absSetSize (absOp a) | a <- reps4 ]
    concTot =
      sum [ fromIntegral (Set.size (Set.fromList (map concOp (C.toList a))))
          | a <- reps4
          ]

binaryResultFiltered ::
  String ->
  (C.Clp 4 -> C.Clp 4 -> C.Clp 4) ->
  (Natural -> Natural -> Maybe Natural) ->
  Result
binaryResultFiltered name absOp concOp = Result name absTot concTot
  where
    absTot =
      sum [ absSetSize (absOp a b) | a <- reps4, b <- reps4 ]
    concTot =
      sum [ fromIntegral (Set.size (Set.fromList
              [ z | x <- C.toList a, y <- C.toList b
                  , Just z <- [concOp x y] ]))
          | a <- reps4, b <- reps4
          ]

binaryResult ::
  String ->
  (C.Clp 4 -> C.Clp 4 -> C.Clp 4) ->
  (Natural -> Natural -> Natural) ->
  Result
binaryResult name absOp concOp =
  binaryResultFiltered name absOp (\x y -> Just (concOp x y))

------------------------------------------------------------------------
-- Concrete operations

cMask :: Natural -> Natural
cMask x = x .&. mask4

cAdd, cMul, cAnd, cOr, cXor :: Natural -> Natural -> Natural
cAdd x y = cMask (x + y)
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

------------------------------------------------------------------------
-- Per-op results

allResults :: [Result]
allResults =
  [ unaryResult "negate" (C.negate w4) cNegate
  , binaryResult "add" (C.add w4) cAdd
  , Result "scale" sAbs sConc
  , binaryResult "mul" (C.mul w4) cMul
  , binaryResultFiltered "udiv" (C.udiv w4) cUdivPartial
  , binaryResultFiltered "urem" (C.urem w4) cUremPartial
  , binaryResultFiltered "sdiv" (C.sdiv w4) cSdivPartial
  , binaryResultFiltered "srem" (C.srem w4) cSremPartial
  , binaryResult "udivSmtlib" (C.udivSmtlib w4) cUdivSmtlib
  , binaryResult "uremSmtlib" (C.uremSmtlib w4) cUremSmtlib
  , binaryResult "sdivSmtlib" (C.sdivSmtlib w4) cSdivSmtlib
  , binaryResult "sremSmtlib" (C.sremSmtlib w4) cSremSmtlib
  , unaryResult "not" (C.not w4) cNot
  , binaryResult "and" (C.and w4) cAnd
  , binaryResult "or"  (C.or  w4) cOr
  , binaryResult "xor" (C.xor w4) cXor
  , binaryResult "shl"  (C.shl  w4) cShl
  , binaryResult "lshr" (C.lshr w4) cLshr
  , binaryResult "ashr" (C.ashr w4) cAshr
  , binaryResult "rol"  (C.rol  w4) cRol
  , binaryResult "ror"  (C.ror  w4) cRor
  ]
  where
    -- 'scale' takes an Integer constant; aggregate over k in [0, 15].
    sAbs  = sum [ absSetSize (C.scale w4 (toInteger k) a)
                | k <- [0 .. mask4], a <- reps4 ]
    sConc = sum [ fromIntegral (Set.size (Set.fromList
                    [ cScale k x | x <- C.toList a ]))
                | k <- [0 .. mask4], a <- reps4 ]

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

csvPath :: FilePath
csvPath = "test/CLP/precision.csv"

main :: IO ()
main = do
  let actual = renderCsv allResults
  update <- (== Just "1") <$> lookupEnv "WHAT4_UPDATE_TEST_EXPECTATIONS"
  if update
    then do
      writeFile csvPath actual
      putStrLn ("Wrote " ++ csvPath)
      exitSuccess
    else do
      expected <- readFile csvPath
      if expected == actual
        then do
          putStrLn ("OK: " ++ csvPath ++ " is up to date")
          exitSuccess
        else do
          hPutStrLn stderr $
            csvPath ++ " is out of date. Expected:\n"
            ++ expected ++ "\nActual:\n" ++ actual
            ++ "\nRun with WHAT4_UPDATE_TEST_EXPECTATIONS=1 to refresh."
          exitFailure
