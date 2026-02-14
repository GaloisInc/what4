{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Gen
  ( GenConfig(..)
  , SomeWidth(..)
  , defaultGenConfig
  , genExprBuilderAPI
  , genBool
  , genBVAtWidth
  , genBVLit
  ) where

import Data.Parameterized.NatRepr (NatRepr, knownNat, natValue, type (<=), addNat, someNat, withKnownNat)
import Data.Parameterized.Some (Some(..))
import qualified Data.BitVector.Sized as BV
import Hedgehog (Gen)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import What4.BaseTypes (BaseBoolType, BaseBVType)
import qualified What4.Interface as WI
import Who2.ExprBuilderAPI (ExprBuilderAPI(..))

-- | A bitvector width with its constraint
data SomeWidth where
  SomeWidth :: (1 <= w) => NatRepr w -> SomeWidth

instance Show SomeWidth where
  show (SomeWidth w) = "SomeWidth " ++ show (natValue w)

-- | Configuration for expression generation
data GenConfig = GenConfig
  { gcMaxDepth :: Int
  , gcBVWidths :: [SomeWidth]  -- Supported bitvector widths
  , gcNumBoolVars :: Int       -- Number of boolean bound variables
  , gcNumBVVars :: Int         -- Number of bitvector bound variables per width
  , gcEnableDivisionOps :: Bool -- Whether to generate division/remainder operations (can produce undefined behavior)
  }

-- | Default configuration: depth 5, widths 8/16/32, 3 vars of each type, division enabled
-- Note: Widths must be multiples of 4 for SMT-LIB2 hexadecimal serialization
defaultGenConfig :: GenConfig
defaultGenConfig = GenConfig
  { gcMaxDepth = 5
  , gcBVWidths = [SomeWidth (knownNat @8), SomeWidth (knownNat @16), SomeWidth (knownNat @32)]
  , gcNumBoolVars = 3
  , gcNumBVVars = 3
  , gcEnableDivisionOps = False
    -- False to avoid UB in tests (div by zero)
  }

-- | Generate a random expression with any result type
genExprBuilderAPI :: GenConfig -> Gen (Some ExprBuilderAPI)
genExprBuilderAPI cfg = Gen.sized $ \size ->
  if size <= 0
  then genLeaf cfg
  else Gen.frequency
    [ (2, genLeaf cfg)
    , (8, Gen.scale (`div` 2) (genNode cfg))
    ]

-- | Generate a leaf expression (constants/literals/bound variables)
genLeaf :: GenConfig -> Gen (Some ExprBuilderAPI)
genLeaf cfg = Gen.frequency
  [ (1, genBoolLeaf cfg)
  , (4, genBVLeaf cfg)
  ]

-- | Generate a non-leaf expression
genNode :: GenConfig -> Gen (Some ExprBuilderAPI)
genNode cfg = Gen.frequency
  [ (2, Some <$> genBoolNode cfg)
  , (8, genBVNode cfg)
  ]

-- | Generate a Boolean leaf (constant or bound variable)
genBoolLeaf :: GenConfig -> Gen (Some ExprBuilderAPI)
genBoolLeaf cfg =
  if gcNumBoolVars cfg == 0
  then Gen.element [Some TruePred, Some FalsePred]
  else Gen.frequency
    [ (1, Gen.element [Some TruePred, Some FalsePred])
    , (2, genBoolBoundVar cfg)
    ]

-- | Generate a Boolean bound variable
genBoolBoundVar :: GenConfig -> Gen (Some ExprBuilderAPI)
genBoolBoundVar cfg = do
  varIdx <- Gen.int (Range.linear 0 (gcNumBoolVars cfg - 1))
  pure $ Some (BoundVarBool varIdx)

-- | Generate a BV leaf (literal or bound variable) with random width
genBVLeaf :: GenConfig -> Gen (Some ExprBuilderAPI)
genBVLeaf cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  if gcNumBVVars cfg == 0
  then Some <$> genBVLit w
  else Gen.frequency
    [ (1, Some <$> genBVLit w)
    , (2, Some <$> genBVBoundVar cfg w)
    ]

-- | Generate a BV bound variable at specific width
genBVBoundVar :: (1 <= w) => GenConfig -> NatRepr w -> Gen (ExprBuilderAPI (BaseBVType w))
genBVBoundVar cfg w = do
  varIdx <- Gen.int (Range.linear 0 (gcNumBVVars cfg - 1))
  pure $ BoundVarBV w varIdx

-- | Generate a BV literal at specific width
genBVLit :: forall w. (1 <= w) => NatRepr w -> Gen (ExprBuilderAPI (BaseBVType w))
genBVLit w = do
  let maxVal = 2 ^ (natValue w) - 1
  val <- Gen.integral (Range.linear 0 maxVal)
  pure $ BVLit w (BV.mkBV w val)

-- | Generate a Boolean expression
genBool :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBool cfg = Gen.sized $ \size ->
  if size <= 0
  then genBoolConst cfg
  else Gen.frequency
    [ (1, genBoolConst cfg)
    , (4, Gen.scale (`div` 2) (genBoolNode cfg))
    ]

-- | Generate a Boolean leaf (constant or bound variable)
genBoolConst :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBoolConst cfg =
  if gcNumBoolVars cfg == 0
  then Gen.element [TruePred, FalsePred]
  else Gen.frequency
    [ (1, Gen.element [TruePred, FalsePred])
    , (2, do varIdx <- Gen.int (Range.linear 0 (gcNumBoolVars cfg - 1))
             pure $ BoundVarBool varIdx)
    ]

-- | Generate a Boolean expression node
genBoolNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBoolNode cfg = Gen.choice
  [ do x <- Gen.small (genBool cfg)
       pure $ NotPred x
  , do x <- Gen.small (genBool cfg)
       y <- Gen.small (genBool cfg)
       pure $ AndPred x y
  , do x <- Gen.small (genBool cfg)
       y <- Gen.small (genBool cfg)
       pure $ OrPred x y
  , do x <- Gen.small (genBool cfg)
       y <- Gen.small (genBool cfg)
       pure $ XorPred x y
  , do c <- Gen.small (genBool cfg)
       t <- Gen.small (genBool cfg)
       e <- Gen.small (genBool cfg)
       pure $ ItePred c t e
  , genBVUltNode cfg
  , genBVSltNode cfg
  , genBVEqNode cfg
  ]

-- | Helpers to generate BV comparison operations
genBVUltNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBVUltNode cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  x <- Gen.small (genBVAtWidth cfg w)
  y <- Gen.small (genBVAtWidth cfg w)
  pure $ BVUlt x y

genBVSltNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBVSltNode cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  x <- Gen.small (genBVAtWidth cfg w)
  y <- Gen.small (genBVAtWidth cfg w)
  pure $ BVSlt x y

genBVEqNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBVEqNode cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  x <- Gen.small (genBVAtWidth cfg w)
  y <- Gen.small (genBVAtWidth cfg w)
  pure $ BVEq x y

-- | Generate a BV expression node with random width
genBVNode :: GenConfig -> Gen (Some ExprBuilderAPI)
genBVNode cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  Some <$> genBVNodeAtWidth cfg w

-- | Generate a BV expression at specific width
genBVAtWidth :: forall w. (1 <= w) => GenConfig -> NatRepr w -> Gen (ExprBuilderAPI (BaseBVType w))
genBVAtWidth cfg w = Gen.sized $ \size ->
  if size <= 0
  then genBVLeafAtWidth cfg w
  else Gen.frequency
    [ (1, genBVLeafAtWidth cfg w)
    , (4, Gen.scale (`div` 2) (genBVNodeAtWidth cfg w))
    ]

-- | Generate a BV leaf (literal or bound variable) at specific width
genBVLeafAtWidth :: forall w. (1 <= w) => GenConfig -> NatRepr w -> Gen (ExprBuilderAPI (BaseBVType w))
genBVLeafAtWidth cfg w =
  if gcNumBVVars cfg == 0
  then genBVLit w
  else Gen.frequency
    [ (1, genBVLit w)
    , (2, genBVBoundVar cfg w)
    ]

-- | Generate a BV expression node at specific width
genBVNodeAtWidth :: forall w. (1 <= w) => GenConfig -> NatRepr w -> Gen (ExprBuilderAPI (BaseBVType w))
genBVNodeAtWidth cfg w =
  let baseOps =
        [ do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVAdd x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVSub x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVMul x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             pure $ BVNeg x
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVAndBits x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVOrBits x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVXorBits x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             pure $ BVNotBits x
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVShl x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVLshr x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVAshr x y
        , do c <- Gen.small (genBool cfg)
             t <- Gen.small (genBVAtWidth cfg w)
             e <- Gen.small (genBVAtWidth cfg w)
             pure $ BVIte c t e
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVRol x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVRor x y
        ]
      divisionOps =
        [ do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVUdiv x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVUrem x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVSdiv x y
        , do x <- Gen.small (genBVAtWidth cfg w)
             y <- Gen.small (genBVAtWidth cfg w)
             pure $ BVSrem x y
        ]
      allOps = if gcEnableDivisionOps cfg
               then baseOps ++ divisionOps
               else baseOps
      widthChangingOps =
        [ -- BVSelect: select w bits starting at index 1 from a larger bitvector
          case someNat (natValue w) of
            Just (Some w') | Just WI.Refl <- WI.testEquality w w' ->
              -- Select from a bitvector that's at least w+1 bits wide
              case someNat (natValue w + 1) of
                Just (Some n) ->
                  withKnownNat n $
                  case (WI.testLeq (knownNat @1) n, WI.testLeq (addNat (knownNat @1) w) n) of
                    (Just WI.LeqProof, Just WI.LeqProof) -> do
                      x <- Gen.small (genBVAtWidth cfg n)
                      pure $ BVSelect (knownNat @1) w x
                    _ -> Gen.discard
                Nothing -> Gen.discard
            _ -> Gen.discard
        -- BVZext: zero-extend a smaller bitvector to width w
        , case natValue w of
            v | v >= 2 ->
              case someNat (v `div` 2) of
                Just (Some u) ->
                  withKnownNat u $
                  case WI.testLeq (knownNat @1) u of
                    Just WI.LeqProof ->
                      case WI.testLeq (addNat u (knownNat @1)) w of
                        Just WI.LeqProof -> do
                          x <- Gen.small (genBVAtWidth cfg u)
                          pure $ BVZext w x
                        Nothing -> Gen.discard
                    Nothing -> Gen.discard
                Nothing -> Gen.discard
            _ -> Gen.discard
        -- BVSext: sign-extend a smaller bitvector to width w
        , case natValue w of
            v | v >= 2 ->
              case someNat (v `div` 2) of
                Just (Some u) ->
                  withKnownNat u $
                  case WI.testLeq (knownNat @1) u of
                    Just WI.LeqProof ->
                      case WI.testLeq (addNat u (knownNat @1)) w of
                        Just WI.LeqProof -> do
                          x <- Gen.small (genBVAtWidth cfg u)
                          pure $ BVSext w x
                        Nothing -> Gen.discard
                    Nothing -> Gen.discard
                Nothing -> Gen.discard
            _ -> Gen.discard
        -- BVConcat: concat two smaller bitvectors to get width w
        , case natValue w of
            v | v >= 2 ->
              let u = v `div` 2
                  v2 = v - u
              in case (someNat u, someNat v2) of
                (Just (Some u'), Just (Some v')) ->
                  withKnownNat u' $
                  withKnownNat v' $
                  case (WI.testLeq (knownNat @1) u', WI.testLeq (knownNat @1) v') of
                    (Just WI.LeqProof, Just WI.LeqProof) ->
                      case WI.testLeq (knownNat @1) (addNat u' v') of
                        Just WI.LeqProof ->
                          case WI.testEquality w (addNat u' v') of
                            Just WI.Refl -> do
                              x <- Gen.small (genBVAtWidth cfg u')
                              y <- Gen.small (genBVAtWidth cfg v')
                              pure $ BVConcat x y
                            Nothing -> Gen.discard
                        Nothing -> Gen.discard
                    _ -> Gen.discard
                _ -> Gen.discard
            _ -> Gen.discard
        ]
  in Gen.choice (allOps ++ widthChangingOps)
