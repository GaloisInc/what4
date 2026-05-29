-- | Direct property tests for the internal helpers underlying
-- 'What4.Domains.BV.Strides.meet'\'s Diophantine path. These pin down the
-- algebraic spec of 'eGCD', 'ceilDivPos'\/'floorDivPos', and
-- 'solveLinearDiophantine' itself, which 'correct_meet' cannot exercise
-- directly.
module Strides.Internal (tests) where

import qualified Test.Tasty as TT

import qualified What4.Domains.BV.Strides.Internal as SI
import           What4.Domains.Verification (chooseBool, chooseInteger, property)
import           VerifyBindings (genTest)

tests :: TT.TestTree
tests = TT.testGroup "Strides Internal"
  [ TT.testGroup "eGCD"
    [ genTest "Bezout identity" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, n, m) = SI.eGCD a b
           pure (property (n * a + m * b == g))
    , genTest "g is nonnegative" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, _, _) = SI.eGCD a b
           pure (property (g >= 0))
    , genTest "g divides both inputs" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, _, _) = SI.eGCD a b
           pure $ property $
             if g == 0
               then a == 0 && b == 0
               else a `mod` g == 0 && b `mod` g == 0
    , genTest "matches Prelude.gcd" $
        do a <- chooseInteger (-256, 256)
           b <- chooseInteger (-256, 256)
           let (g, _, _) = SI.eGCD a b
           pure (property (g == gcd a b))
    ]
  , TT.testGroup "ceilDivPos / floorDivPos"
    [ genTest "ceilDivPos bounds" $
        do x <- chooseInteger (-1024, 1024)
           y <- chooseInteger (1, 2 ^ (32 :: Int))
           let q = SI.ceilDivPos x y
           pure (property (q * y >= x && (q - 1) * y < x))
    , genTest "floorDivPos bounds" $
        do x <- chooseInteger (-1024, 1024)
           y <- chooseInteger (1, 2 ^ (32 :: Int))
           let q = SI.floorDivPos x y
           pure (property (q * y <= x && (q + 1) * y > x))
    ]
  , TT.testGroup "solveLinearDiophantine"
    [ genTest "sound" $
        do a    <- chooseInteger (1, 2 ^ (32 :: Int))
           b    <- chooseInteger (1, 2 ^ (32 :: Int))
           aMax <- chooseInteger (1, 2 ^ (32 :: Int))
           bMax <- chooseInteger (1, 2 ^ (32 :: Int))
           x0   <- chooseInteger (0, aMax)
           y0   <- chooseInteger (0, bMax)
           let c = a * x0 - b * y0
           pure $
             if c == 0
               then property True
               else case SI.solveLinearDiophantine a b c aMax bMax of
                      Nothing     -> property False
                      Just (x, y) ->
                        property (0 <= x && x <= aMax
                               && 0 <= y && y <= bMax
                               && a * x - b * y == c)
    , genTest "complete (brute-force)" $
        do a    <- chooseInteger (1, 64)
           b    <- chooseInteger (1, 64)
           aMax <- chooseInteger (1, 64)
           bMax <- chooseInteger (1, 64)
           cAbs <- chooseInteger (1, 64)
           sign <- chooseBool
           let c = if sign then cAbs else -cAbs
               exists = or [ a * x - b * y == c
                           | x <- [0 .. aMax], y <- [0 .. bMax]
                           ]
           pure $ property $
             case (exists, SI.solveLinearDiophantine a b c aMax bMax) of
               (True,  Just _ ) -> True
               (False, Nothing) -> True
               _                -> False
    , genTest "finds endpoint intersection" $
        do a <- chooseInteger (1, 2 ^ (32 :: Int))
           k <- chooseInteger (1, 2 ^ (32 :: Int))
           let aMax = k
               bMax = 1
               c    = a * k
           pure $ property $
             case SI.solveLinearDiophantine a 1 c aMax bMax of
               Just _  -> True
               Nothing -> False
    ]
  ]
