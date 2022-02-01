{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : GenWhat4Expr
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : kquick@galois.com

This module provides Hedgehog generators for What4 expression values
that have associated Haskell counterparts; the Haskell value predicts
the What4 value on evaluation.

The What4 expression is often generated from a Haskell value
evaluation, so the "distance" between the tests and the implementation
might be seen as fairly small.  However, there is a lot of
simplification and subterm-elimination that is attempted in What4
expressions; this testing can verify the expected *functional*
behavior of the expressions as various simplifications and
implementation adjustments are made.

Because these are generated expressions, they don't tend to shrink as
much one would expect (e.g.  @(5 + 1)@ will not be shrunk to @6@)
because that requires domain-specific expression evaluation.  When
failures occur, it can be helpful to temporarily edit out portions of
these generators to attempt simplification.
-}

module GenWhat4Expr where

import           Data.Bits
import qualified Data.BitVector.Sized as BV
import           Data.Maybe ( fromMaybe, isJust )
import           Data.Word
import           GHC.Natural
import           GHC.TypeNats ( KnownNat )
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Internal.Gen as IGen
import qualified Hedgehog.Range as Range
import           Test.Tasty.HUnit
import           What4.Interface


-- | A convenience class to extract the description string and haskell
-- value (and type) for any type of TestExpr.
class IsTestExpr x where
  type HaskellTy x
  desc :: x -> String
  testval :: x -> HaskellTy x

  -- n.b. cannot ad What4BTy, because the target (SymExpr) is a type
  -- synonym for a type family and type family instances cannot
  -- specify a type synonym as a target.
  --
  -- data What4BTy x :: BaseType -- -> Type
  -- type What4BTy x :: Type -> Type

  -- testexpr :: forall sym. (IsExprBuilder sym) => x -> sym -> IO (What4BTy x sym)

pdesc :: IsTestExpr x => x -> String
pdesc s = "(" <> desc s <> ")"

----------------------------------------------------------------------

-- Somewhat awkward, but when using Gen.subtermN for Gen.recursive,
-- each of the subterms is required to have the same type as the
-- result of the recursive term.  This is fine for uniform values
-- (e.g. simply-typed lambda calculi) but for a DSL like the What4
-- IsExprBuilder this means that even though there are separate
-- generators here for each subtype the results must be wrapped in a
-- common type that can hold all the 't' results from 'SymExpr sym
-- t'... the 'TestExpr' type here.  There's a lot of expectation of
-- which value is present when unwrapping (this is just test code),
-- and there various uses of Hedgehog 'Gen.filter' to ensure the right
-- value is returned even in the face of shrinking: when shrinking a
-- recursive term (e.g. "natEq x y") the result is a 'Pred sym', but
-- shrinking will try to eliminate the 'natEq' wrapper and end up
-- trying to return 'x' or 'y', which is a 'SymNat sym' instead.

data TestExpr = TE_Bool PredTestExpr
              | TE_Int  IntTestExpr
              | TE_BV8  BV8TestExpr
              | TE_BV16 BV16TestExpr
              | TE_BV32 BV32TestExpr
              | TE_BV64 BV64TestExpr

-- Projection functions that return Nothing if there is a constructor mismatch.

boolTestExprMaybe :: TestExpr -> Maybe PredTestExpr
boolTestExprMaybe = \case
  TE_Bool p -> Just p
  _ -> Nothing

intTestExprMaybe :: TestExpr -> Maybe IntTestExpr
intTestExprMaybe = \case
  TE_Int i -> Just i
  _ -> Nothing

bv8TestExprMaybe :: TestExpr -> Maybe BV8TestExpr
bv8TestExprMaybe = \case
  TE_BV8 bv8 -> Just bv8
  _ -> Nothing

bv16TestExprMaybe :: TestExpr -> Maybe BV16TestExpr
bv16TestExprMaybe = \case
  TE_BV16 bv16 -> Just bv16
  _ -> Nothing

bv32TestExprMaybe :: TestExpr -> Maybe BV32TestExpr
bv32TestExprMaybe = \case
  TE_BV32 bv32 -> Just bv32
  _ -> Nothing

bv64TestExprMaybe :: TestExpr -> Maybe BV64TestExpr
bv64TestExprMaybe = \case
  TE_BV64 bv64 -> Just bv64
  _ -> Nothing

-- Projection functions that `error` if there is a constructor mismatch.
-- Use these with caution.

fromBoolTestExpr :: HasCallStack => TestExpr -> PredTestExpr
fromBoolTestExpr = fromMaybe (error "Expected TE_Bool") . boolTestExprMaybe

fromIntTestExpr :: HasCallStack => TestExpr -> IntTestExpr
fromIntTestExpr = fromMaybe (error "Expected TE_Int") . intTestExprMaybe

fromBV8TestExpr :: HasCallStack => TestExpr -> BV8TestExpr
fromBV8TestExpr = fromMaybe (error "Expected TE_BV8") . bv8TestExprMaybe

fromBV16TestExpr :: HasCallStack => TestExpr -> BV16TestExpr
fromBV16TestExpr = fromMaybe (error "Expected TE_BV16") . bv16TestExprMaybe

fromBV32TestExpr :: HasCallStack => TestExpr -> BV32TestExpr
fromBV32TestExpr = fromMaybe (error "Expected TE_BV32") . bv32TestExprMaybe

fromBV64TestExpr :: HasCallStack => TestExpr -> BV64TestExpr
fromBV64TestExpr = fromMaybe (error "Expected TE_BV64") . bv64TestExprMaybe

-- Constructor predicates

isBoolTestExpr, isIntTestExpr,
  isBV8TestExpr, isBV16TestExpr, isBV32TestExpr, isBV64TestExpr
  :: TestExpr -> Bool

isBoolTestExpr = isJust . boolTestExprMaybe
isIntTestExpr = isJust . intTestExprMaybe
isBV8TestExpr = isJust . bv8TestExprMaybe
isBV16TestExpr = isJust . bv16TestExprMaybe
isBV32TestExpr = isJust . bv32TestExprMaybe
isBV64TestExpr = isJust . bv64TestExprMaybe


----------------------------------------------------------------------

data PredTestExpr =
  PredTest { preddsc :: String
           , predval :: Bool
           , predexp :: forall sym. (IsExprBuilder sym) => sym -> IO (Pred sym)
           }

instance IsTestExpr PredTestExpr where
  type HaskellTy PredTestExpr = Bool
  desc = preddsc
  testval = predval


genBoolCond :: (HasCallStack, Monad m) => GenT m TestExpr
genBoolCond = Gen.recursive Gen.choice
  [
    return $ TE_Bool $ PredTest "true" True $ return . truePred
  , return $ TE_Bool $ PredTest "false" False $ return . falsePred
  ]
  $
  let boolTerm = IGen.filterT isBoolTestExpr genBoolCond
      intTerm = IGen.filterT isIntTestExpr genIntTestExpr
      bv8Term = IGen.filterT isBV8TestExpr genBV8TestExpr
      bv16Term = IGen.filterT isBV16TestExpr genBV16TestExpr
      bv32Term = IGen.filterT isBV32TestExpr genBV32TestExpr
      bv64Term = IGen.filterT isBV64TestExpr genBV64TestExpr
      subBoolTerm2 gen = Gen.subterm2 boolTerm boolTerm
                         (\xt yt -> let x = fromBoolTestExpr xt
                                        y = fromBoolTestExpr yt in
                                    TE_Bool $ gen x y)
      subBoolTerm3 gen = Gen.subterm3 boolTerm boolTerm boolTerm
                         (\xt yt zt -> let x = fromBoolTestExpr xt
                                           y = fromBoolTestExpr yt
                                           z = fromBoolTestExpr zt in
                                       TE_Bool $ gen x y z)
      subIntTerms2 gen = Gen.subterm2 intTerm intTerm (\xt yt -> let x = fromIntTestExpr xt
                                                                     y = fromIntTestExpr yt in
                                                                 TE_Bool $ gen x y)
      -- subBV16Terms2 gen = Gen.subterm2 bv16Term bv16Term (\xt yt -> let x = fromBV16TestExpr xt
      --                                                                   y = fromBV16TestExpr yt in
      --                                                               TE_Bool $ gen x y)
      -- subBV8Terms2 gen = Gen.subterm2 bv8Term bv8Term (\xt yt -> let x = fromBV8TestExpr xt
      --                                                                y = fromBV8TestExpr yt in
      --                                                            TE_Bool $ gen x y)
  in
  [
    Gen.subterm genBoolCond
    (\itct -> let itc = fromBoolTestExpr itct in
              TE_Bool $ PredTest ("not " <> pdesc itc)
              (not $ testval itc)
              (\sym -> notPred sym =<< predexp itc sym))

  , subBoolTerm2
    (\x y ->
       PredTest ("and " <> pdesc x <> " " <> pdesc y)
       (testval x && testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   andPred sym x' y'
       ))

  , subBoolTerm2
    (\x y ->
       PredTest ("or " <> pdesc x <> " " <> pdesc y)
       (testval x || testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   orPred sym x' y'
       ))

  , subBoolTerm2
    (\x y ->
       PredTest ("eq " <> pdesc x <> " " <> pdesc y)
       (testval x == testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   eqPred sym x' y'
       ))

  , subBoolTerm2
    (\x y ->
       PredTest ("xor " <> pdesc x <> " " <> pdesc y)
       (testval x `xor` testval y)
       (\sym -> do x' <- predexp x sym
                   y' <- predexp y sym
                   xorPred sym x' y'
       ))

  , subBoolTerm3
    (\c x y ->
       PredTest ("ite " <> pdesc c <> " " <> pdesc x <> " " <> pdesc y)
       (if testval c then testval x else testval y)
       (\sym -> do c' <- predexp c sym
                   x' <- predexp x sym
                   y' <- predexp y sym
                   itePred sym c' x' y'
       ))

  , subIntTerms2
    (\x y ->
        PredTest ("intEq " <> pdesc x <> " " <> pdesc y)
        (testval x == testval y)
        (\sym -> do x' <- intexpr x sym
                    y' <- intexpr y sym
                    intEq sym x' y'
        ))

  , subIntTerms2
    (\x y ->
        PredTest (pdesc x <> " int.<= " <> pdesc y)
        (testval x <= testval y)
        (\sym -> do x' <- intexpr x sym
                    y' <- intexpr y sym
                    intLe sym x' y'
        ))

  , subIntTerms2
    (\x y ->
        PredTest (pdesc x <> " int.< " <> pdesc y)
        (testval x < testval y)
        (\sym -> do x' <- intexpr x sym
                    y' <- intexpr y sym
                    intLt sym x' y'
        ))

  , Gen.subterm2 intTerm bv16Term
    -- Note [natTerm]: natTerm is used as the index into
    -- bv16term. This is somewhat inefficient, but saves the
    -- administrative overhead of another TestExpr member.  However,
    -- the NatExpr could be greater than the bit range, so mod the
    -- result if necessary.  Also note that the testBitBV uses an
    -- actual Natural, not a What4 Nat, so the natval is used and the
    -- natexpr is ignored.
    (\it vt -> TE_Bool $  -- KWQ: bvsized
      let i = fromIntTestExpr it
          v = fromBV16TestExpr vt
          ival = fromInteger (testval i `mod` 16) in
      PredTest
      (pdesc v <> "[" <> show ival <> "]")
      (testBit (testval v) (fromEnum ival))
      (\sym -> testBitBV sym ival =<< bvexpr v sym))

  ]
  ++ bvPredExprs bv8Term fromBV8TestExpr bv8expr 8
  ++ bvPredExprs bv16Term fromBV16TestExpr bvexpr 16
  ++ bvPredExprs bv32Term fromBV32TestExpr bv32expr 32
  ++ bvPredExprs bv64Term fromBV64TestExpr bv64expr 64


bvPredExprs :: ( Monad m
               , HaskellTy bvtestexpr ~ Integer
               , IsTestExpr bvtestexpr
               , 1 <= w
               )
            => GenT m TestExpr
            -> (TestExpr -> bvtestexpr)
            -> (bvtestexpr
                -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w)))
            -> Natural
            -> [GenT m TestExpr]
bvPredExprs bvTerm projTE expr width =
  let subBVTerms2 gen = Gen.subterm2 bvTerm bvTerm
                        (\x y -> TE_Bool $ gen (projTE x) (projTE y))
      mask = (.&.) (2^width - 1)
      uBV v = if v >= 0 then v else 2^width + v
      sBV v = let norm = if v >= 0 then v else mask (v - 2^width)
              in if norm >= (2^(width-1)) then norm - 2^width else norm
      pfx o = "bv" <> show width <> "." <> o
  in
  [
    subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvEq", pdesc y])
        (uBV (testval x) == uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvEq sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvNe", pdesc y])
        (uBV (testval x) /= uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvNe sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUlt", pdesc y])
        (uBV (testval x) < uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUlt sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUle", pdesc y])
        (uBV (testval x) <= uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUle sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUge", pdesc y])
        (uBV (testval x) >= uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUge sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvUgt", pdesc y])
        (uBV (testval x) > uBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvUgt sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSlt", pdesc y])
        (sBV (testval x) < sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSlt sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSle", pdesc y])
        (sBV (testval x) <= sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSle sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSge", pdesc y])
        (sBV (testval x) >= sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSge sym x' y'
        ))

  , subBVTerms2
    (\x y ->
        PredTest (unwords [pdesc x, pfx "bvSgt", pdesc y])
        (sBV (testval x) > sBV (testval y))
        (\sym -> do x' <- expr x sym
                    y' <- expr y sym
                    bvSgt sym x' y'
        ))

  , Gen.subterm bvTerm
    (\vt -> TE_Bool $ let v = projTE vt in
        PredTest
        (pfx "isneg? " <> pdesc v)
        (mask (testval v) < 0 || mask (testval v) >= 2^(width-1))
        (\sym -> bvIsNeg sym =<< expr v sym))

  , Gen.subterm bvTerm
    (\vt -> TE_Bool $ let v = projTE vt in
        PredTest
        (pfx "isNonZero? " <> pdesc v)
        (testval v /= 0)
        (\sym -> bvIsNonzero sym =<< expr v sym))

  ]


----------------------------------------------------------------------

data IntTestExpr = IntTestExpr { intdesc :: String
                               , intval  :: Integer
                               , intexpr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymInteger sym)
                               }

instance IsTestExpr IntTestExpr where
  type HaskellTy IntTestExpr = Integer
  desc = intdesc
  testval = intval

genIntTestExpr :: Monad m => GenT m TestExpr
genIntTestExpr = Gen.recursive Gen.choice
  [
    do n <- Gen.integral $ Range.constant (-3) 3  -- keep the range small, or will never see dup values for natEq
       return $ TE_Int $ IntTestExpr (show n) n $ \sym -> intLit sym n
  ]
  $
  let intTerm = IGen.filterT isIntTestExpr genIntTestExpr
      intTermNZ = IGen.filterT isIntNZTestExpr genIntTestExpr
      isIntNZTestExpr = \case
        TE_Int n -> testval n /= 0
        _ -> False
      subIntTerms2 gen = Gen.subterm2 intTerm intTerm
                           (\xt yt -> let x = fromIntTestExpr xt
                                          y = fromIntTestExpr yt in
                                      TE_Int $ gen x y)
      subIntTerms2nz gen = Gen.subterm2 intTerm intTermNZ
                           (\xt yt -> let x = fromIntTestExpr xt
                                          y = fromIntTestExpr yt in
                                      TE_Int $ gen x y)
  in
  [
    subIntTerms2 (\x y -> IntTestExpr (pdesc x <> " int.+ " <> pdesc y)
                          (testval x + testval y)
                          (\sym -> do x' <- intexpr x sym
                                      y' <- intexpr y sym
                                      intAdd sym x' y'
                          ))
  , subIntTerms2
    (\x y -> IntTestExpr (pdesc x <> " int.- " <> pdesc y)
             (testval x - testval y)
             (\sym -> do x' <- intexpr x sym
                         y' <- intexpr y sym
                         intSub sym x' y'
             ))
  , subIntTerms2
    (\x y -> IntTestExpr (pdesc x <> " int.* " <> pdesc y)
             (testval x * testval y)
             (\sym -> do x' <- intexpr x sym
                         y' <- intexpr y sym
                         intMul sym x' y'
             ))
  , subIntTerms2nz  -- nz on 2nd to avoid divide-by-zero
    (\x y -> IntTestExpr (pdesc x <> " int./ " <> pdesc y)
             (if testval y >= 0 then
                 testval x `div` testval y
              else
                 negate (testval x `div` negate (testval y)))
             (\sym -> do x' <- intexpr x sym
                         y' <- intexpr y sym
                         intDiv sym x' y'
             ))
  , subIntTerms2nz  -- nz on 2nd to avoid divide-by-zero
    (\x y -> IntTestExpr (pdesc x <> " int.mod " <> pdesc y)
             (testval x `mod` abs (testval y))
             (\sym -> do x' <- intexpr x sym
                         y' <- intexpr y sym
                         intMod sym x' y'
             ))
  , Gen.subterm3
    (IGen.filterT isBoolTestExpr genBoolCond)
    intTerm intTerm
    (\ct xt yt ->
      let c = fromBoolTestExpr ct
          x = fromIntTestExpr xt
          y = fromIntTestExpr yt in
      TE_Int $ IntTestExpr
      (pdesc c <> " int.? " <> pdesc x <> " : " <> pdesc y)
      (if testval c then testval x else testval y)
      (\sym -> do c' <- predexp c sym
                  x' <- intexpr x sym
                  y' <- intexpr y sym
                  intIte sym c' x' y'
      ))
  ]

----------------------------------------------------------------------

-- TBD: genIntTestExpr :: Monad m => GenT m TestExpr


----------------------------------------------------------------------

allbits8, allbits16, allbits32, allbits64 :: Integer
allbits8  = (2 :: Integer) ^ (8 :: Integer) - 1
allbits16 = (2 :: Integer) ^ (16 :: Integer) - 1
allbits32 = (2 :: Integer) ^ (32 :: Integer) - 1
allbits64 = (2 :: Integer) ^ (64 :: Integer) - 1


genBV8val :: Monad m => GenT m Integer
genBV8val = Gen.choice
            [
              -- keep the range small, or will never see dup values
              Gen.integral $ Range.constantFrom 0 (-10) 10
            , Gen.integral $ Range.constant (128-1) (128+1)
            , Gen.integral $ Range.constant (allbits8-2) allbits8
            ]

data BV8TestExpr = BV8TestExpr
  { bv8desc :: String
  , bv8val  :: Integer
  , bv8expr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 8)
  }

instance IsTestExpr BV8TestExpr where
  type HaskellTy BV8TestExpr = Integer
  desc = bv8desc
  testval = bv8val

genBV8TestExpr :: Monad m => GenT m TestExpr
genBV8TestExpr = let ret8 = return . TE_BV8 in
  Gen.recursive Gen.choice
  [
    do n <- genBV8val
       ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> bvLit sym knownRepr (BV.mkBV knownNat n)
  , ret8 $ BV8TestExpr ("0`8") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits8
    in ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits8 `shiftR` 1
    in ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits8 `xor` (allbits8 `shiftR` 1)
    in ret8 $ BV8TestExpr (show n <> "`8") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  bvTGExprs (tgen8 bvTermGens)
  ++
  bvTGMixedExprs bvTermGens 8


genBV16val :: Monad m => GenT m Integer
genBV16val = Gen.choice
             [
               -- keep the range small, or will never see dup values
               Gen.integral $ Range.constantFrom 0 (-10) 10
             , Gen.integral $ Range.constant (allbits8-1) (allbits8+2)
             , Gen.integral $ Range.constant ((-1) * (allbits8+2)) ((-1) * (allbits8-1))
             , Gen.integral $ Range.constant (allbits16-2) allbits16
             ]

data BV16TestExpr =
  BV16TestExpr { bvdesc :: String
               , bvval  :: Integer
               , bvexpr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 16)
               }

instance IsTestExpr BV16TestExpr where
  type HaskellTy BV16TestExpr = Integer
  desc = bvdesc
  testval = bvval

genBV16TestExpr :: Monad m => GenT m TestExpr
genBV16TestExpr = let ret16 = return . TE_BV16 in
  Gen.recursive Gen.choice
  [
    do n <- genBV16val
       ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> bvLit sym knownRepr (BV.mkBV knownNat n)
  , ret16 $ BV16TestExpr ("0`16") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits16
    in ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits16 `shiftR` 1
    in ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits16 `xor` (allbits16 `shiftR` 1)
    in ret16 $ BV16TestExpr (show n <> "`16") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  bvTGExprs (tgen16 bvTermGens)
  ++
  bvTGMixedExprs bvTermGens 16


genBV32val :: Monad m => GenT m Integer
genBV32val = Gen.choice
             [
               -- keep the range small, or will never see dup values
               Gen.integral $ Range.constantFrom 0 (-10) 10
             , Gen.integral $ Range.constant (allbits8-1) (allbits8+2)
             , Gen.integral $ Range.constant (allbits16-1) (allbits16+2)
             , Gen.integral $ Range.constant ((-1) * (allbits16+2)) ((-1) * (allbits16-1))
             , Gen.integral $ Range.constant (allbits32-2) allbits32
             ]


data BV32TestExpr =
  BV32TestExpr { bv32desc :: String
               , bv32val  :: Integer
               , bv32expr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 32)
               }

instance IsTestExpr BV32TestExpr where
  type HaskellTy BV32TestExpr = Integer
  desc = bv32desc
  testval = bv32val

genBV32TestExpr :: Monad m => GenT m TestExpr
genBV32TestExpr = let ret32 = return . TE_BV32 in
  Gen.recursive Gen.choice
  [
    do n <- genBV32val
       ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> bvLit sym knownRepr (BV.mkBV knownNat n)
  , ret32 $ BV32TestExpr ("0`32") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits32
    in ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits32 `shiftR` 1
    in ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits32 `xor` (allbits32 `shiftR` 1)
    in ret32 $ BV32TestExpr (show n <> "`32") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  bvTGExprs (tgen32 bvTermGens)
  ++
  bvTGMixedExprs bvTermGens 32


genBV64val :: Monad m => GenT m Integer
genBV64val = Gen.choice
             [
               -- keep the range small, or will never see dup values
               Gen.integral $ Range.constantFrom 0 (-10) 10
             , Gen.integral $ Range.constant (allbits8-1) (allbits8+2)
             , Gen.integral $ Range.constant (allbits16-1) (allbits16+2)
             , Gen.integral $ Range.constant (allbits32-1) (allbits32+2)
             , Gen.integral $ Range.constant ((-1) * (allbits32+2)) ((-1) * (allbits32-1))
             , Gen.integral $ Range.constant (allbits64-2) allbits64
             ]


data BV64TestExpr =
  BV64TestExpr { bv64desc :: String
               , bv64val  :: Integer
               , bv64expr :: forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym 64)
               }

instance IsTestExpr BV64TestExpr where
  type HaskellTy BV64TestExpr = Integer
  desc = bv64desc
  testval = bv64val

genBV64TestExpr :: Monad m => GenT m TestExpr
genBV64TestExpr = let ret64 = return . TE_BV64 in
  Gen.recursive Gen.choice
  [
    do n <- genBV64val
       ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> bvLit sym knownRepr (BV.mkBV knownNat n)
  , ret64 $ BV64TestExpr ("0`64") 0 $ \sym -> minUnsignedBV sym knownRepr
  , let n = allbits64
    in ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> maxUnsignedBV sym knownRepr
  , let n = allbits64 `shiftR` 1
    in ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> maxSignedBV sym knownRepr
  , let n = allbits64 `xor` (allbits64 `shiftR` 1)
    in ret64 $ BV64TestExpr (show n <> "`64") n $ \sym -> minSignedBV sym knownRepr
  ]
  $
  bvTGExprs (tgen64 bvTermGens)
  ++
  bvTGMixedExprs bvTermGens 64


-- | For a particular bitwidth, the BVTermGen structure provides the
-- various definitions of term generators, constructors and
-- projectors, What4 expression extractors, and width designations.
data BVTermGen m bvtestexpr w word = BVTermGen
  {
    genTerm :: GenT m TestExpr
  , conBVT :: bvtestexpr -> TestExpr
  , projBVT :: TestExpr -> bvtestexpr
  , subBVTCon :: String -> Integer
              -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w))
              -> bvtestexpr
  , symExpr :: bvtestexpr
            -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w))
  , bitWidth :: Natural
  , toBVWord :: (Integer -> word)
  }

-- | This combines the information about BVTermGen for all of the
-- standard widths
data BVTermsGen m = BVTermsGen
  {
    tgen8 :: BVTermGen m BV8TestExpr 8 Word8
  , tgen16 :: BVTermGen m BV16TestExpr 16 Word16
  , tgen32 :: BVTermGen m BV32TestExpr 32 Word32
  , tgen64 :: BVTermGen m BV64TestExpr 64 Word64
  }

bvTermGens :: Monad m => BVTermsGen m
bvTermGens =
  let g8 = BVTermGen
           (IGen.filterT isBV8TestExpr genBV8TestExpr)
           TE_BV8
           fromBV8TestExpr
           BV8TestExpr
           bv8expr
           8
           fromIntegral
      g16 = BVTermGen
            (IGen.filterT isBV16TestExpr genBV16TestExpr)
            TE_BV16
            fromBV16TestExpr
            BV16TestExpr
            bvexpr
            16
            fromIntegral
      g32 = BVTermGen
            (IGen.filterT isBV32TestExpr genBV32TestExpr)
            TE_BV32
            fromBV32TestExpr
            BV32TestExpr
            bv32expr
            32
            fromIntegral
      g64 = BVTermGen
            (IGen.filterT isBV64TestExpr genBV64TestExpr)
            TE_BV64
            fromBV64TestExpr
            BV64TestExpr
            bv64expr
            64
            fromIntegral
            -- n.b. toEnum . fromEnum doesn't work for very large
            -- Word64 values (-1, -2, high-bit set?), so use
            -- fromIntegral instead (probably faster?)
  in BVTermsGen g8 g16 g32 g64


bvTGExprs :: ( Monad m
             , HaskellTy bvtestexpr ~ Integer
             , IsTestExpr bvtestexpr
             , 1 <= w
             , KnownNat w
             , Integral word
             , FiniteBits word
             )
          => BVTermGen m bvtestexpr w word
          -> [GenT m TestExpr]
bvTGExprs gt = bvExprs (genTerm gt) (conBVT gt) (projBVT gt) (subBVTCon gt)
                       (symExpr gt) (bitWidth gt) (toBVWord gt)

bvExprs :: ( Monad m
           , HaskellTy bvtestexpr ~ Integer
           , IsTestExpr bvtestexpr
           , 1 <= w
           , KnownNat w
           , Integral word
           , Bits word
           , FiniteBits word
           )
        => GenT m TestExpr
        -> (bvtestexpr -> TestExpr)
        -> (TestExpr -> bvtestexpr)
        -> (String -> Integer
            -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w))
            -> bvtestexpr)
        -> (bvtestexpr
            -> (forall sym. (IsExprBuilder sym) => sym -> IO (SymBV sym w)))
        -> Natural
        -> (HaskellTy bvtestexpr -> word)
        -> [GenT m TestExpr]
bvExprs bvTerm conTE projTE teSubCon expr width toWord =
  let subBVTerms1 gen = Gen.subterm bvTerm (conTE . gen . projTE)
      subBVTerms2 gen = Gen.subterm2 bvTerm bvTerm
                        (\x y -> conTE $ gen (projTE x) (projTE y))
      subBVTerms2nz gen = Gen.subterm2 bvTerm bvTermNZ
                          (\x y -> conTE $ gen (projTE x) (projTE y))
      bvTermNZ = do t <- projTE <$> bvTerm
                    -- adjust 0 to +1 to avoid divide-by-zero.  A
                    -- Gen.filterT tends to lead to non-termination
                    -- here
                    return $ if testval t == 0
                             then conTE $ teSubCon
                                  (pdesc t <> " +1")
                                  (testval t + 1)
                                  (\sym -> do lit1 <- bvLit sym knownRepr (BV.one knownNat)

                                              orig <- expr t sym
                                              bvAdd sym orig lit1)
                             else conTE t
      mask = (.&.) (2^width - 1)
      uBV v = if v >= 0 then v else 2^width + v
      sBV v = let norm = if v >= 0 then v else mask (v - 2^width)
              in if norm >= (2^(width-1)) then norm - 2^width else norm
      pfx o = "bv" <> show width <> "." <> o
  in
  [
    subBVTerms1
    (\x -> teSubCon (pfx "neg " <> pdesc x)
           (mask ((-1) * testval x))
           (\sym -> bvNeg sym =<< expr x sym))

  , subBVTerms1
    (\x -> teSubCon (pfx "not " <> pdesc x)
           (mask (complement $ testval x))
           (\sym -> bvNotBits sym =<< expr x sym))

  , subBVTerms2
    (\x y -> teSubCon (pdesc x <> " " <> pfx "+ " <> pdesc y)
             (mask (testval x + testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvAdd sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "-", pdesc y])
             (mask (testval x - testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvSub sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "*", pdesc y])
             (mask (testval x * testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvMul sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "u/", pdesc y])
             (mask (uBV (testval x) `quot` uBV (testval y)))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvUdiv sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "urem", pdesc y])
             (mask (uBV (testval x) `rem` uBV (testval y)))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvUrem sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "s/", pdesc y])
             (let x' = sBV $ testval x
                  y' = sBV $ testval y
              in mask (x' `quot` y'))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvSdiv sym x' y'))

  , subBVTerms2nz
    (\x y -> teSubCon (unwords [pdesc x, pfx "srem", pdesc y])
             (let x' = sBV $ testval x
                  y' = sBV $ testval y
              in mask (x' `rem` y'))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvSrem sym x' y'))

  , Gen.subterm3
    (IGen.filterT isBoolTestExpr genBoolCond)
    bvTerm bvTerm
    (\ct lt rt -> conTE $
    let c = fromBoolTestExpr ct
        l = projTE lt
        r = projTE rt
    in teSubCon
       (unwords [pdesc c, pfx "?", pdesc l, ":", pdesc r])
       (if testval c then testval l else testval r)
       (\sym -> do c' <- predexp c sym
                   l' <- expr l sym
                   r' <- expr r sym
                   bvIte sym c' l' r'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "rol", pdesc y])
             (let x' = toWord $ uBV $ testval x
                  y' = fromEnum $ uBV $ testval y
              in mask (toInteger (x' `rotateL` y')))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvRol sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "ror", pdesc y])
             (let x' = toWord $ uBV $ testval x
                  y' = fromEnum $ uBV $ testval y
              in mask (toInteger (x' `rotateR` y')))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvRor sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "&", pdesc y])
             (mask (testval x .&. testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvAndBits sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "|", pdesc y])
             (mask (testval x .|. testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvOrBits sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "xor", pdesc y])
             (mask (testval x `xor` testval y))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvXorBits sym x' y'))

  , let intTerm = IGen.filterT isIntTestExpr genIntTestExpr
        boolTerm = IGen.filterT isBoolTestExpr genBoolCond
    in
      Gen.subterm3 bvTerm intTerm boolTerm $
      -- see Note [natTerm]
      \bvt nt bt ->
        let bv = projTE bvt
            n = fromIntTestExpr nt
            b = fromBoolTestExpr bt
            nval = fromInteger (testval n `mod` toInteger width)
            ival = fromIntegral nval :: Int
        in conTE $ teSubCon
           (pdesc bv <> "[" <> show nval <> "]" <> pfx ":=" <> pdesc b)
           (if testval b
            then setBit (testval bv) ival
            else clearBit (testval bv) ival)
           (\sym -> do bv' <- expr bv sym
                       b' <- predexp b sym
                       bvSet sym bv' nval b')

  , let boolTerm = IGen.filterT isBoolTestExpr genBoolCond
    in
      Gen.subterm boolTerm $
      \bt ->
        let b = fromBoolTestExpr bt in
        -- technically bvFill also takes a NatRepr for the output
        -- width, but due to the arrangement of these expression
        -- generators, it will just generate the size specified for
        -- the current width
        conTE $ teSubCon
        (pfx "=" <> pdesc b <> "..")
        (if testval b then mask (-1) else mask 0)
        (\sym -> bvFill sym knownRepr =<< predexp b sym)

  , subBVTerms1
    (\x -> teSubCon (pfx "bvPopCount " <> pdesc x)
           (fromIntegral $ popCount $ mask $ testval x)
           (\sym -> bvPopcount sym =<< expr x sym))

  , subBVTerms1
    (\x -> teSubCon (pfx "bvCountLeadingZeros " <> pdesc x)
           (fromIntegral $ countLeadingZeros $ toWord $ uBV $ mask $ testval x)
           (\sym -> bvCountLeadingZeros sym =<< expr x sym))

  , subBVTerms1
    (\x -> teSubCon (pfx "bvCountTrailingZeros " <> pdesc x)
           (fromIntegral $ countTrailingZeros $ toWord $ uBV $ mask $ testval x)
           (\sym -> bvCountTrailingZeros sym =<< expr x sym))

  -- TBD: carrylessMultiply

  , subBVTerms1
    (\x -> teSubCon
           (pfx "bvSelect @0[" <> pdesc x <> "]")
           (mask (testval x))
           (\sym -> do x' <- expr x sym
                       bvSelect sym (knownRepr :: NatRepr 0) knownRepr x'))

  -- TODO: bvTrunc doesn't allow the no-op/same-size operation
  -- , subBVTerms1
  --   (\x -> teSubCon
  --          (pfx "bvTrunc " <> pdesc x)
  --          (mask (testval x))
  --          (\sym -> do x' <- expr x sym
  --                      bvTrunc sym knownRepr x'))

  -- TODO: bvZext doesn't allow the no-op/same-size operation
  -- , subBVTerms1
  --   (\x -> teSubCon
  --          (pfx "bvZext " <> pdesc x)
  --          (mask (testval x))
  --          (\sym -> do x' <- expr x sym
  --                      bvZext sym knownRepr x'))

  -- TODO: bvSext doesn't allow the no-op/same-size operation
  -- , subBVTerms1
  --   (\x -> teSubCon
  --          (pfx "bvSext " <> pdesc x)
  --          (mask (testval x))
  --          (\sym -> do x' <- expr x sym
  --                      bvSext sym knownRepr x'))


  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "<<", pdesc y])
             (mask (uBV (testval x) `shiftL` (fromEnum $ min (toInteger width) $ uBV $ testval y)))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvShl sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "lsr", pdesc y])
             (let s = fromEnum $ min (toInteger width) $ uBV $ testval y
              in mask (uBV (testval x) `shiftR` s))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvLshr sym x' y'))

  , subBVTerms2
    (\x y -> teSubCon (unwords [pdesc x, pfx "asr", pdesc y])
             (let s = fromEnum $ min (toInteger width) $ uBV $ testval y
              in mask (sBV (testval x) `shiftR` s))
             (\sym -> do x' <- expr x sym
                         y' <- expr y sym
                         bvAshr sym x' y'))

  ]


bvTGMixedExprs :: Monad m => BVTermsGen m -> Natural -> [GenT m TestExpr]
bvTGMixedExprs termGens tgtWidth =
  case tgtWidth of
    8 -> bvTGMixedExprs_Double (tgen8 termGens) (tgen16 termGens) ++
         bvTGMixedExprs_Quadruple (tgen8 termGens) (tgen32 termGens)
    16 -> bvTGMixedExprs_Half (tgen16 termGens) (tgen8 termGens) ++
          bvTGMixedExprs_Double (tgen16 termGens) (tgen32 termGens) ++
          bvTGMixedExprs_Quadruple (tgen16 termGens) (tgen64 termGens)
    32 -> bvTGMixedExprs_Half (tgen32 termGens) (tgen16 termGens) ++
          bvTGMixedExprs_QuarterHalf (tgen32 termGens) (tgen16 termGens) (tgen8 termGens) ++
          bvTGMixedExprs_Double (tgen32 termGens) (tgen64 termGens)
    64 -> bvTGMixedExprs_Half (tgen64 termGens) (tgen32 termGens) ++
          bvTGMixedExprs_QuarterHalf (tgen64 termGens) (tgen32 termGens) (tgen16 termGens)
    _ -> error $ "Unsupported width for mixed BV expressions: " <> show tgtWidth


bvTGMixedExprs_Half :: ( Monad m
                       , 1 <= w
                       , w + 1 <= w + w
                       , KnownNat (w + w)
                       , HaskellTy bvtestexpr ~ Integer
                       , IsTestExpr bvtestexpr
                       , HaskellTy bvtestexpr_h ~ Integer
                       , IsTestExpr bvtestexpr_h
                       )
                    => BVTermGen m bvtestexpr (w + w) word
                    -> BVTermGen m bvtestexpr_h w word_h
                    -> [GenT m TestExpr]
bvTGMixedExprs_Half thisTG halfTG =
  let pfx o = "bv" <> (show $ bitWidth thisTG) <> "." <> o
      halfWidth = bitWidth halfTG
      halfMask = (.&.) (2^halfWidth - 1)
      width = bitWidth thisTG
      mask = (.&.) (2^width - 1)
      halfHiBit = (.&.) (2^(halfWidth - 1))
  in
    -- output size must match the size of thisTG
    [
      Gen.subterm2 (genTerm halfTG) (genTerm halfTG) $
      (\gen x y -> conBVT thisTG $ gen (projBVT halfTG x) (projBVT halfTG y)) $
      (\x y -> subBVTCon thisTG
               (pfx "bvConcat " <> pdesc x <> " " <> pdesc y)
               (let x' = halfMask (testval x)
                    y' = halfMask (testval y)
                in (x' `shiftL` (fromEnum halfWidth)) .|. y')
               (\sym -> do x' <- symExpr halfTG x sym
                           y' <- symExpr halfTG y sym
                           bvConcat sym x' y'))

    , Gen.subterm (genTerm halfTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvZext " <> pdesc (projBVT halfTG x))
             (let x' = testval (projBVT halfTG x)
               in (halfMask x'))
             (\sym -> do x' <- symExpr halfTG (projBVT halfTG x) sym
                         bvZext sym knownRepr x'))

    , Gen.subterm (genTerm halfTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSext " <> pdesc (projBVT halfTG x))
             (let x' = halfMask $ testval (projBVT halfTG x)
                  hiBits = mask (-1) `xor` halfMask (-1)
              in if halfHiBit x' == 0 then x' else (hiBits .|. x'))
             (\sym -> do x' <- symExpr halfTG (projBVT halfTG x) sym
                         bvSext sym knownRepr x'))
    ]

bvTGMixedExprs_QuarterHalf :: ( Monad m
                              , 1 <= w
                              , 1 <= w + w
                              , 1 <= w + w + w + w
                              , (w + (w + w)) ~ ((w + w) + w)
                              , 1 <= ((w + w) + w)
                              , (w + 1) <= w + w + w + w
                              , KnownNat (w + w + w + w)
                              , HaskellTy bvtestexpr ~ Integer
                              , IsTestExpr bvtestexpr
                              , HaskellTy bvtestexpr_h ~ Integer
                              , IsTestExpr bvtestexpr_h
                              , HaskellTy bvtestexpr_q ~ Integer
                              , IsTestExpr bvtestexpr_q
                              )
                           => BVTermGen m bvtestexpr (w + w + w + w) word
                           -> BVTermGen m bvtestexpr_h (w + w) word_h
                           -> BVTermGen m bvtestexpr_q w word_q
                           -> [GenT m TestExpr]
bvTGMixedExprs_QuarterHalf thisTG halfTG quarterTG =
  let pfx o = "bv" <> (show $ bitWidth thisTG) <> "." <> o
      halfWidth = bitWidth halfTG
      halfMask = (.&.) (2^halfWidth - 1)
      quarterWidth = bitWidth quarterTG
      quarterMask = (.&.) (2^quarterWidth - 1)
      quarterHiBit = (.&.) (2^(quarterWidth - 1))
      width = bitWidth thisTG
      mask = (.&.) (2^width - 1)
  in
    [
      Gen.subterm3 (genTerm quarterTG) (genTerm halfTG) (genTerm quarterTG) $
      (\gen x y z -> conBVT thisTG $
                     gen (projBVT quarterTG x)
                         (projBVT halfTG y)
                         (projBVT quarterTG z)) $
      (\x y z -> subBVTCon thisTG
                 (pfx "bvConcat " <> pdesc x <> " " <>
                  pfx "bvConcat " <> pdesc y <> " " <> pdesc z)
                 (let x' = quarterMask (testval x)
                      y' = halfMask (testval y)
                      z' = quarterMask (testval z)
                      s1 = fromEnum halfWidth
                      s2 = fromEnum quarterWidth
                  in ((((x' `shiftL` s1) .|. y') `shiftL` s2) .|. z'))
                 (\sym -> do x' <- symExpr quarterTG x sym
                             y' <- symExpr halfTG y sym
                             z' <- symExpr quarterTG z sym
                             xy <- bvConcat sym x' y'
                             bvConcat sym xy z'))

    -- already did bvZext and bvSext with half-size in
    -- bvTGMixedExprs_Half, so just test extensions from quarter size
    -- here.

    , Gen.subterm (genTerm quarterTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvZext " <> pdesc (projBVT quarterTG x))
             (let x' = testval (projBVT quarterTG x)
               in (quarterMask x'))
             (\sym -> do x' <- symExpr quarterTG (projBVT quarterTG x) sym
                         bvZext sym knownRepr x'))

    , Gen.subterm (genTerm quarterTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSext " <> pdesc (projBVT quarterTG x))
             (let x' = quarterMask $ testval (projBVT quarterTG x)
                  hiBits = mask (-1) `xor` quarterMask (-1)
              in if quarterHiBit x' == 0 then x' else (hiBits .|. x'))
             (\sym -> do x' <- symExpr quarterTG (projBVT quarterTG x) sym
                         bvSext sym knownRepr x'))
    ]


bvTGMixedExprs_Double :: ( Monad m
                         , 1 <= w
                         , 0 + w <= w + w
                         , 1 + w <= w + w  -- bvSelect --v
                         , w + 1 <= w + w  -- bvTrunc ---^
                         , 2 + w <= w + w
                         , 7 + w <= w + w
                         , KnownNat w
                         , HaskellTy bvtestexpr ~ Integer
                         , IsTestExpr bvtestexpr
                         , HaskellTy bvtestexpr_d ~ Integer
                         , IsTestExpr bvtestexpr_d
                         )
                      => BVTermGen m bvtestexpr w word
                      -> BVTermGen m bvtestexpr_d (w + w) word_d
                      -> [GenT m TestExpr]
bvTGMixedExprs_Double thisTG dblTG =
  let pfx o = "bv" <> (show $ bitWidth thisTG) <> "." <> o
      mask = (.&.) (2^(bitWidth thisTG) - 1)
  in
    [

      -- The bvSelect offset and size are NatReprs, so the type must
      -- be known at compile time, thus these values cannot be
      -- generated via hedgehog property generation functions.  The
      -- size must be the size of the current conBVT result, and
      -- bvSelect requres that offset + size < width of input
      -- value. There are a few hard-coded offsets used here that
      -- should be valid for all input BV sizes >= 16 and output BV
      -- sizes >= 8:
      --
      --   0, 1, 2, 7

      Gen.subterm (genTerm dblTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @0[" <> pdesc (projBVT dblTG x) <> "]")
             (mask ((testval (projBVT dblTG x)) `shiftR` 0))
             (\sym -> do x' <- symExpr dblTG (projBVT dblTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 0) knownRepr x'))

    , Gen.subterm (genTerm dblTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @1[" <> pdesc (projBVT dblTG x) <> "]")
             (mask ((testval (projBVT dblTG x)) `shiftR` 1))
             (\sym -> do x' <- symExpr dblTG (projBVT dblTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 1) knownRepr x'))

    , Gen.subterm (genTerm dblTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @2[" <> pdesc (projBVT dblTG x) <> "]")
             (mask ((testval (projBVT dblTG x)) `shiftR` 2))
             (\sym -> do x' <- symExpr dblTG (projBVT dblTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 2) knownRepr x'))

    , Gen.subterm (genTerm dblTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @7[" <> pdesc (projBVT dblTG x) <> "]")
             (mask ((testval (projBVT dblTG x)) `shiftR` 7))
             (\sym -> do x' <- symExpr dblTG (projBVT dblTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 7) knownRepr x'))

    , Gen.subterm (genTerm dblTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvTrunc " <> pdesc (projBVT dblTG x))
             (mask (testval (projBVT dblTG x)))
             (\sym -> do x' <- symExpr dblTG (projBVT dblTG x) sym
                         bvTrunc sym knownRepr x'))
    ]

bvTGMixedExprs_Quadruple :: ( Monad m
                         , 1 <= w
                         , 0 + w <= w + w + w + w
                         , 1 + w <= w + w + w + w  -- bvSelect --v
                         , w + 1 <= w + w + w + w  -- bvTrunc ---^
                         , 2 + w <= w + w + w + w
                         , 7 + w <= w + w + w + w
                         , 12 + w <= w + w + w + w
                         , 19 + w <= w + w + w + w
                         , KnownNat w
                         , HaskellTy bvtestexpr ~ Integer
                         , IsTestExpr bvtestexpr
                         , HaskellTy bvtestexpr_d ~ Integer
                         , IsTestExpr bvtestexpr_d
                         )
                      => BVTermGen m bvtestexpr w word
                      -> BVTermGen m bvtestexpr_d (w + w + w + w) word_d
                      -> [GenT m TestExpr]
bvTGMixedExprs_Quadruple thisTG quadTG =
  let pfx o = "bv" <> (show $ bitWidth thisTG) <> "." <> o
      mask = (.&.) (2^(bitWidth thisTG) - 1)
  in
    [
      -- The bvSelect offset and size are NatReprs, so the type must
      -- be known at compile time, thus these values cannot be
      -- generated via hedgehog property generation functions.  The
      -- size must be the size of the current conBVT result, and there
      -- are a few hard-coded offsets used here that should be valid
      -- for all BV sizes >= 32:
      --
      --   0, 1, 2, 7, 12, 19

      Gen.subterm (genTerm quadTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @0[" <> pdesc (projBVT quadTG x) <> "]")
             (mask ((testval (projBVT quadTG x)) `shiftR` 0))
             (\sym -> do x' <- symExpr quadTG (projBVT quadTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 0) knownRepr x'))

    , Gen.subterm (genTerm quadTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @1[" <> pdesc (projBVT quadTG x) <> "]")
             (mask ((testval (projBVT quadTG x)) `shiftR` 1))
             (\sym -> do x' <- symExpr quadTG (projBVT quadTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 1) knownRepr x'))

    , Gen.subterm (genTerm quadTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @2[" <> pdesc (projBVT quadTG x) <> "]")
             (mask ((testval (projBVT quadTG x)) `shiftR` 2))
             (\sym -> do x' <- symExpr quadTG (projBVT quadTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 2) knownRepr x'))

    , Gen.subterm (genTerm quadTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @7[" <> pdesc (projBVT quadTG x) <> "]")
             (mask ((testval (projBVT quadTG x)) `shiftR` 7))
             (\sym -> do x' <- symExpr quadTG (projBVT quadTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 7) knownRepr x'))

    , Gen.subterm (genTerm quadTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @12[" <> pdesc (projBVT quadTG x) <> "]")
             (mask ((testval (projBVT quadTG x)) `shiftR` 12))
             (\sym -> do x' <- symExpr quadTG (projBVT quadTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 12) knownRepr x'))

    , Gen.subterm (genTerm quadTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvSelect @19[" <> pdesc (projBVT quadTG x) <> "]")
             (mask ((testval (projBVT quadTG x)) `shiftR` 19))
             (\sym -> do x' <- symExpr quadTG (projBVT quadTG x) sym
                         bvSelect sym (knownRepr :: NatRepr 19) knownRepr x'))

    -- bvTrunc output size must match the size of thisTG

    , Gen.subterm (genTerm quadTG)
      (\x -> conBVT thisTG $
             subBVTCon thisTG
             (pfx "bvTrunc " <> pdesc (projBVT quadTG x))
             (mask (testval (projBVT quadTG x)))
             (\sym -> do x' <- symExpr quadTG (projBVT quadTG x) sym
                         bvTrunc sym knownRepr x'))
    ]



-- TBD: BV operations returning a (Pred,BV) pair will need another TestExpr
-- representation: addUnsignedOF, addSignedOF, subUnsignedOF,
-- subSignedOF, mulUnsignedOF, mulSignedOF

-- TBD: BV operations returning a (BV,BV) pair will need another
-- TestExpr representation: unsignedWideMultiplyBV, signedWideMultiplyBV

-- TBD: struct operations
-- TBD: array operations
-- TBD: Lossless conversions
-- TBD: Lossless combinators
-- TBD: Lossy conversions
-- TBD: Lossy (non-injective) combinators
-- TBD: Bitvector operations (intSetWidth, uintSetWidth, intToUInt)
-- TBD: string operations
-- TBD: real operations
-- TBD: IEEE-754 floating-point operations
-- TBD: Cplx operations
-- TBD: misc functions in Interface.hs
