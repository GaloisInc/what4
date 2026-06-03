{-
Module      : PrecisionRegression.Arith
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Per-op precision results for the arithmetic interval domain at width 4. The
CSV is at @test\/PrecisionRegression\/arith.csv@.
-}

{-# LANGUAGE DataKinds #-}

module PrecisionRegression.Arith
  ( arithEnum
  , results
  , csvPath
  ) where

import           Control.Exception (assert)
import           Numeric.Natural (Natural)

import           Data.Parameterized.NatRepr (maxUnsigned)

import qualified What4.Domains.BV.Arith as A

import           PrecisionRegression.Common

-- | Enumerate every distinct 'A.Domain' at width 4.
enumArith4 :: [A.Domain 4]
enumArith4 =
  [ assert (A.proper w4 d) d
  | d <- A.top w4
       : [ A.interval mask (toInteger lo) (toInteger sz)
         | lo <- [0 .. mask4]
         , sz <- [0 .. mask4 - 1]
         ]
  ]
  where
    mask = maxUnsigned w4

arithToList :: A.Domain 4 -> [Natural]
arithToList d = [ x | x <- [0 .. mask4], A.member d (toInteger x) ]

arithEnum :: DomainEnum (A.Domain 4)
arithEnum = DomainEnum (dedup arithToList enumArith4) arithToList

results :: [Result]
results =
  [ leqResult arithEnum "leq" A.leq
  , unaryResult arithEnum "negate" A.negate cNegate
  , binaryResult arithEnum "add" A.add cAdd
  , binaryResult arithEnum "sub" (\a b -> A.add a (A.negate b)) cSub
  , scaleResult arithEnum A.scale
  , binaryResult arithEnum "mul" A.mul cMul
  , binaryResultFiltered arithEnum "udiv" A.udiv cUdivPartial
  , binaryResultFiltered arithEnum "urem" A.urem cUremPartial
  , binaryResultFiltered arithEnum "sdiv" (A.sdiv w4) cSdivPartial
  , binaryResultFiltered arithEnum "srem" (A.srem w4) cSremPartial
  , binaryResult arithEnum "udivSmtlib" A.udivSmtlib cUdivSmtlib
  , binaryResult arithEnum "uremSmtlib" A.uremSmtlib cUremSmtlib
  , binaryResult arithEnum "sdivSmtlib" (A.sdivSmtlib w4) cSdivSmtlib
  , binaryResult arithEnum "sremSmtlib" (A.sremSmtlib w4) cSremSmtlib
  , unaryResult arithEnum "not" A.not cNot
  , binaryResult arithEnum "shl" (A.shl w4) cShl
  , binaryResult arithEnum "lshr" (A.lshr w4) cLshr
  , binaryResult arithEnum "ashr" (A.ashr w4) cAshr
  , latticeResult arithEnum "join" A.join cJoin
  , latticeResult arithEnum "meet" A.meet cMeet
  ]

csvPath :: FilePath
csvPath = "test/PrecisionRegression/arith.csv"
