{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : ExprsTest test
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : kquick@galois.com

This module provides some verification of selected What4 Expressions.
There are a number of simplifications, subsumptions, and other rewrite
rules used for these What4 expressions; this module is intended to
verify the correctness of those.
-}

import           Control.Monad.IO.Class ( liftIO )
import           Data.Bits
import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Nonce
import           GenWhat4Expr
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog.Alt
import           What4.Concrete
import           What4.Expr
import           What4.Interface
import           What4.Internal (assertionsEnabled)

import Bool (boolTests)
import qualified UnionFind (tests)

type IteExprBuilder t fs = ExprBuilder t EmptyExprBuilderState fs

withTestSolver :: (forall t. IteExprBuilder t (Flags FloatIEEE) -> IO a) -> IO a
withTestSolver f = withIONonceGenerator $ \nonce_gen ->
  f =<< newExprBuilder FloatIEEERepr EmptyExprBuilderState nonce_gen


-- | Test natDiv and natMod properties described at their declaration
-- site in What4.Interface
testIntDivModProps :: TestTree
testIntDivModProps =
  testProperty "d <- intDiv sym x y; m <- intMod sym x y ===> y * d + m == x and 0 <= m < y" $
  property $ do
    xn <- forAll $ Gen.integral $ Range.linear (negate 1000) (1000 :: Integer)
    -- no zero; avoid div-by-zero
    yn <- forAll $ (Gen.choice [ Gen.integral $ Range.linear 1 (2000 :: Integer)
                               , Gen.integral $ Range.linear (-2000) (-1)])
    dm <- liftIO $ withTestSolver $ \sym -> do
      x <- intLit sym xn
      y <- intLit sym yn
      d <- intDiv sym x y
      m <- intMod sym x y
      return (asConcrete d, asConcrete m)
    case dm of
      (Just dnc, Just mnc) -> do
        let dn = fromConcreteInteger dnc
        let mn = fromConcreteInteger mnc
        annotateShow (xn, yn, dn, mn)
        yn * dn + mn === xn
        diff mn (\m y -> 0 <= m && m < abs y) yn
      _ -> failure

testInt :: TestTree
testInt = testGroup "int operators"
  [ testProperty "n * m == m * n" $
    property $ do
      n <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      m <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      (nm, mn) <- liftIO $ withTestSolver $ \sym -> do
        n_lit <- intLit sym n
        m_lit <- intLit sym m
        nm <- intMul sym n_lit m_lit
        mn <- intMul sym m_lit n_lit
        return (asConcrete nm, asConcrete mn)
      nm === mn
  , testProperty "|n| >= 0" $
    property $ do
      n_random <- forAll $ Gen.integral $ Range.linear (-1000) 10
      n_abs <- liftIO $ withTestSolver $ \sym -> do
        n <- intLit sym n_random
        n_abs <- intAbs sym n
        return (asConcrete n_abs)
      case fromConcreteInteger <$> n_abs of
        Just nabs -> do
          nabs === abs n_random
          diff nabs (>=) 0
        _ -> failure
  , testIntDivMod
  , testIntMinMax
  ]

testIntMinMax :: TestTree
testIntMinMax = testGroup "int min/max"
  [ testProperty "(j <= c && c <= i) -> intMax j i == intMax i j == i" $
    property $ do
      c <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      liftIO $ withTestSolver $ \sym -> do 
        j <- freshBoundedInt sym (safeSymbol "j") Nothing (Just c)
        i <- freshBoundedInt sym (safeSymbol "i") (Just c) Nothing
        max_j_i <- intMax sym j i
        res1 <- intEq sym max_j_i i
        asConstantPred res1 @=? Just True
        max_i_j <- intMax sym i j
        res2 <- intEq sym max_i_j i
        asConstantPred res2 @=? Just True
  , testProperty "(lo_i <= i && lo_j <= j) -> (max lo_j lo_j) <= intMax i j" $
    property $ do
      lo_i <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      lo_j <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      liftIO $ withTestSolver $ \sym -> do
        i <- freshBoundedInt sym (safeSymbol "i") (Just lo_i) Nothing
        j <- freshBoundedInt sym (safeSymbol "j") (Just lo_j) Nothing
        lo <- intLit sym (max lo_i lo_j)
        max_i_j <- intMax sym i j
        res1 <- intLe sym lo max_i_j
        asConstantPred res1 @=? Just True
        max_j_i <- intMax sym j i
        res2 <- intLe sym lo max_j_i
        asConstantPred res2 @=? Just True   
  , testProperty "(i <= c && c <= j) -> intMin j i == intMin i j == i" $
    property $ do
      c <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      liftIO $ withTestSolver $ \sym -> do
        j <- freshBoundedInt sym (safeSymbol "j") (Just c) Nothing
        i <- freshBoundedInt sym (safeSymbol "i") Nothing (Just c)
        min_j_i <- intMin sym j i
        res1 <- intEq sym min_j_i i
        asConstantPred res1 @=? Just True
        min_i_j <- intMin sym i j
        res2 <- intEq sym min_i_j i
        asConstantPred res2 @=? Just True
  , testProperty "(i <= hi_i && j <= hi_j) -> intMin i j <= (min hi_j hi_j)" $
    property $ do
      hi_i <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      hi_j <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      liftIO $ withTestSolver $ \sym -> do
        i <- freshBoundedInt sym (safeSymbol "i") Nothing (Just hi_i)
        j <- freshBoundedInt sym (safeSymbol "j") Nothing (Just hi_j)
        hi <- intLit sym (min hi_i hi_j)
        min_i_j <- intMin sym i j
        res1 <- intLe sym min_i_j hi
        asConstantPred res1 @=? Just True
        min_j_i <- intMin sym j i
        res2 <- intLe sym min_j_i hi
        asConstantPred res2 @=? Just True
  ]


testIntDivMod :: TestTree
testIntDivMod = testGroup "integer division and mod"
  [ testProperty "y * (div x y) + (mod x y) == x" $
    property $ do
      x <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      y <- forAll $ Gen.choice -- skip 0
           [ Gen.integral $ Range.linear (-1000) (-1)
           , Gen.integral $ Range.linear 1 1000
           ]
      result <- liftIO $ withTestSolver $ \sym -> do
        x_lit <- intLit sym x
        y_lit <- intLit sym y
        divxy <- intDiv sym x_lit y_lit
        modxy <- intMod sym x_lit y_lit
        return (asConcrete y_lit, asConcrete divxy, asConcrete modxy, asConcrete x_lit)
      case result of
        (Just y_c, Just divxy_c, Just modxy_c, Just x_c) -> do
          let y' = fromConcreteInteger y_c
          let x' = fromConcreteInteger x_c
          let divxy = fromConcreteInteger divxy_c
          let modxy = fromConcreteInteger modxy_c
          y' * divxy + modxy === x'
          diff 0 (<=) modxy
          diff modxy (<) (abs y')
        _ -> failure
  , testProperty "mod x y == mod x (- y) == mod x (abs y)" $
    property $ do
      x <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      y <- forAll $ Gen.choice -- skip 0
           [ Gen.integral $ Range.linear (-1000) (-1)
           , Gen.integral $ Range.linear 1 1000
           ]
      result <- liftIO $ withTestSolver $ \sym -> do
        x_lit <- intLit sym x
        y_lit <- intLit sym y
        modxy <- intMod sym x_lit y_lit
        y_neg <- intLit sym (-y)
        y_abs <- intAbs sym y_lit
        modxNegy <- intMod sym x_lit y_neg
        modxAbsy <- intMod sym x_lit y_abs
        return (asConcrete modxy, asConcrete modxNegy, asConcrete modxAbsy)
      case result of
        (Just modxy_c, Just modxNegy_c, Just modxAbsy_c) -> do
          let modxy = fromConcreteInteger modxy_c
          let modxNegy = fromConcreteInteger modxNegy_c
          let modxAbsy = fromConcreteInteger modxAbsy_c
          annotateShow (modxy, modxNegy)
          modxy === modxNegy
          annotateShow (modxNegy, modxAbsy)
          modxNegy === modxAbsy
        _ -> failure
  , testProperty "div x (-y) == -(div x y)" $
    property $ do
      x <- forAll $ Gen.integral $ Range.linear (-1000) 1000
      y <- forAll $ Gen.choice -- skip 0
           [ Gen.integral $ Range.linear (-1000) (-1)
           , Gen.integral $ Range.linear 1 1000
           ]
      result <- liftIO $ withTestSolver $ \sym -> do
        x_lit <- intLit sym x
        y_lit <- intLit sym y
        divxy <- intDiv sym x_lit y_lit
        y_neg <- intLit sym (-y)
        divxNegy <- intDiv sym x_lit y_neg
        negdivxy <- intNeg sym divxy
        return (asConcrete divxNegy, asConcrete negdivxy)
      case result of
        (Just divxNegy_c, Just negdivxy_c) -> do
          let divxNegy = fromConcreteInteger divxNegy_c
          let negdivxy = fromConcreteInteger negdivxy_c
          divxNegy === negdivxy
        _ -> failure
  ]

testBvIsNeg :: TestTree
testBvIsNeg = testGroup "bvIsNeg"
  [
    -- bvLit value is an Integer; the Integer itself is signed.
    -- Verify that signed Integers count as negative values.

    testCase "-1.32 bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.mkBV knownNat ((-1) .&. allbits32))
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

  , testCase "-1 bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.mkBV knownNat (-1))
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

    -- Check a couple of corner cases

  , testCase "0xffffffff bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.mkBV knownNat allbits32)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

  , testCase "0x80000000 bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.mkBV knownNat 0x80000000)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

  , testCase "0x7fffffff !bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.mkBV knownNat 0x7fffffff)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool False) @=? r

  , testCase "0 !bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.zero knownNat)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool False) @=? r

  , testProperty "bvIsNeg.32" $ property $ do
      i <- forAll $ Gen.integral $ Range.linear (-10) (-1)
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.mkBV knownNat i)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) === r

  , testProperty "!bvIsNeg.32" $ property $ do
      i <- forAll $ Gen.integral $ Range.linear 0 10
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (BV.mkBV knownNat i)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool False) === r
  ]

testInjectiveConversions :: TestTree
testInjectiveConversions = testGroup "injective conversion"
  [ testProperty "realToInteger" $ property $ do
    i <- forAll $ Gen.integral $ Range.linear (-1000) 1000
    liftIO $ withTestSolver $ \sym -> do
      r_lit <- realLit sym (fromIntegral i)
      rti <- realToInteger sym r_lit
      Just i @=? (fromConcreteInteger <$> asConcrete rti)
  , testProperty "bvToInteger" $ property $ do
    i <- forAll $ Gen.integral $ Range.linear 0 255
    liftIO $ withTestSolver $ \sym -> do
      b_lit <- bvLit sym knownRepr (BV.mkBV (knownNat @8) (fromIntegral i))
      int <- bvToInteger sym b_lit
      Just i @=? (fromConcreteInteger <$> asConcrete int)
  , testProperty "sbvToInteger" $ property $ do
    i <- forAll $ Gen.integral $ Range.linear (-128) 127
    liftIO $ withTestSolver $ \sym -> do
      b_lit <- bvLit sym knownRepr (BV.mkBV (knownNat @8) (fromIntegral i))
      int <- sbvToInteger sym b_lit
      Just i @=? (fromConcreteInteger <$> asConcrete int)
  , testProperty "predToBV" $ property $ do
    b <- forAll $ Gen.integral $ Range.linear 0 1
    liftIO $ withTestSolver $ \sym -> do
      let p = if b == 1 then truePred sym else falsePred sym
      let w = knownRepr :: NatRepr 8
      b_lit <- predToBV sym p w
      int <- bvToInteger sym b_lit
      Just b @=? (fromConcreteInteger <$> asConcrete int)
  , testIntegerToBV
  ]

testIntegerToBV :: TestTree
testIntegerToBV = testGroup "integerToBV"
  [ testProperty "bvToInteger (integerToBv x w) == mod x (2^w)" $ property $ do
    x <- forAll $ Gen.integral $ Range.linear (-1000) 1000
    liftIO $ withTestSolver $ \sym -> do
      let w' = 8 :: Integer
      let w = knownRepr :: NatRepr 8
      x_lit <- intLit sym x
      itobv <- integerToBV sym x_lit w
      bvtoi <- bvToInteger sym itobv
      (fromConcreteInteger <$> asConcrete bvtoi) @=? Just (x `mod` 2^w')
  , testProperty "bvToInteger (integerToBV x w) == x when 0 <= x < 2^w" $ property $ do
    let w = 8 :: Integer
    x <- forAll $ Gen.integral $ Range.linear 0 (2^w-1)
    liftIO $ withTestSolver $ \sym -> do
      let w' = knownRepr :: NatRepr 8
      x_lit <- intLit sym x
      itobv <- integerToBV sym x_lit w'
      bvtoi <- bvToInteger sym itobv
      (fromConcreteInteger <$> asConcrete bvtoi) @=? Just x
  , testProperty "sbvToInteger (integerToBV x w) == mod (x + 2^(w-1)) (2^w) - 2^(w-1)" $ property $ do
    let w = 8 :: Integer
    x <- forAll $ Gen.integral $ Range.linear (-1000) 1000
    liftIO $ withTestSolver $ \sym -> do
      let w' = knownRepr :: NatRepr 8
      x_lit <- intLit sym x
      itobv <- integerToBV sym x_lit w'
      sbvtoi <- sbvToInteger sym itobv
      (fromConcreteInteger <$> asConcrete sbvtoi) @=? Just (mod (x + 2^(w-1)) (2^w) - 2^(w-1))
  , testProperty "sbvToInteger (integerToBV x w) == x when -2^(w-1) <= x < 2^(w-1)" $ property $ do
    let w = 8 :: Integer
    x <- forAll $ Gen.integral $ Range.linear (-(2^(w-1))) (2^(w-1)-1)
    liftIO $ withTestSolver $ \sym -> do
      let w' = knownRepr :: NatRepr 8
      x_lit <- intLit sym x
      itobv <- integerToBV sym x_lit w'
      sbvtoi <- sbvToInteger sym itobv
      (fromConcreteInteger <$> asConcrete sbvtoi) @=? Just x
  , testProperty "integerToBV (bvToInteger y) w == y when y is a SymBV sym w" $ property $ do
    x <- forAll $ Gen.integral $ Range.linear (-1000) 1000
    liftIO $ withTestSolver $ \sym -> do
      let w' = knownRepr :: NatRepr 8
      y <- bvLit sym knownRepr (BV.mkBV (knownNat @8) x)
      bvtoi <- bvToInteger sym y
      itobv <- integerToBV sym bvtoi w'
      itobv @=? y
  , testProperty "integerToBV (sbvToInteger y) w == y when y is a SymBV sym w" $ property $ do
    x <- forAll $ Gen.integral $ Range.linear (-1000) 1000
    liftIO $ withTestSolver $ \sym -> do
      let w' = knownRepr :: NatRepr 8
      y <- bvLit sym knownRepr (BV.mkBV (knownNat @8) x)
      sbvtoi <- sbvToInteger sym y
      itobv <- integerToBV sym sbvtoi w'
      itobv @=? y
  ]

----------------------------------------------------------------------

main :: IO ()
main = defaultMain $ testGroup "What4 Expressions"
   [ -- See Note [Asserts] in what4
     testCase "assertions enabled" $ do
       assertsEnabled <- assertionsEnabled
       assertBool "assertions should be enabled" assertsEnabled
  , testIntDivModProps
  , testBvIsNeg
  , testInt
  , testProperty "stringEmpty" $ property $ do
    s <- liftIO $ withTestSolver $ \sym -> do
      s <- stringEmpty sym UnicodeRepr
      return (asConcrete s)
    (fromConcreteString <$> s) === Just ""
  , testInjectiveConversions
  , boolTests
  , UnionFind.tests
  ]
