{-
Module      : PrecisionRegression.Bitwise
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Per-op precision results for the bitwise (tnum) domain at width 4. The CSV
is at @test\/PrecisionRegression\/bitwise.csv@.
-}

{-# LANGUAGE DataKinds #-}

module PrecisionRegression.Bitwise
  ( bitwiseEnum
  , results
  , csvPath
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.|.))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Bitwise as B

import           PrecisionRegression.Common

-- | Enumerate every distinct 'B.Domain' at width 4.
enumBitwise4 :: [B.Domain 4]
enumBitwise4 =
  [ assert (B.proper w4 d) d
  | lo <- [0 .. mask4]
  , hi <- [0 .. mask4]
  , (lo .|. hi) == hi
  , let d = B.range w4 (toInteger lo) (toInteger hi)
  ]

bitwiseToList :: B.Domain 4 -> [Natural]
bitwiseToList d = [ x | x <- [0 .. mask4], B.member d (toInteger x) ]

bitwiseEnum :: DomainEnum (B.Domain 4)
bitwiseEnum = DomainEnum (dedup bitwiseToList enumBitwise4) bitwiseToList

results :: [Result]
results =
  [ leqResult bitwiseEnum "leq" B.leq
  , unaryResult bitwiseEnum "negate" B.negate cNegate
  , binaryResult bitwiseEnum "add" B.add cAdd
  , binaryResult bitwiseEnum "sub" B.sub cSub
  , scaleResult bitwiseEnum B.scale
  , binaryResult bitwiseEnum "mul" B.mul cMul
  , binaryResult bitwiseEnum "mulPrecise" B.mulPrecise cMul
  , binaryResultFiltered bitwiseEnum "udiv" B.udiv cUdivPartial
  , binaryResultFiltered bitwiseEnum "urem" B.urem cUremPartial
  , binaryResultFiltered bitwiseEnum "sdiv" (B.sdiv w4) cSdivPartial
  , binaryResultFiltered bitwiseEnum "srem" (B.srem w4) cSremPartial
  , binaryResultFiltered bitwiseEnum "udivPrecise" (B.udivPrecise w4) cUdivPartial
  , binaryResultFiltered bitwiseEnum "uremPrecise" (B.uremPrecise w4) cUremPartial
  , binaryResult bitwiseEnum "udivSmtlib" B.udivSmtlib cUdivSmtlib
  , binaryResult bitwiseEnum "uremSmtlib" B.uremSmtlib cUremSmtlib
  , binaryResult bitwiseEnum "sdivSmtlib" (B.sdivSmtlib w4) cSdivSmtlib
  , binaryResult bitwiseEnum "sremSmtlib" (B.sremSmtlib w4) cSremSmtlib
  , unaryResult bitwiseEnum "not" B.not cNot
  , binaryResult bitwiseEnum "and" B.and cAnd
  , binaryResult bitwiseEnum "or"  B.or  cOr
  , binaryResult bitwiseEnum "xor" B.xor cXor
  , binaryResult bitwiseEnum "shl"  (B.shlAbstract  w4) cShl
  , binaryResult bitwiseEnum "lshr" (B.lshrAbstract w4) cLshr
  , binaryResult bitwiseEnum "ashr" (B.ashrAbstract w4) cAshr
  , binaryResult bitwiseEnum "rol"  (B.rolAbstract  w4) cRol
  , binaryResult bitwiseEnum "ror"  (B.rorAbstract  w4) cRor
  , latticeResult bitwiseEnum "join" B.join cJoin
  , latticeResult bitwiseEnum "meet" B.meet cMeet
  ]

csvPath :: FilePath
csvPath = "test/PrecisionRegression/bitwise.csv"
