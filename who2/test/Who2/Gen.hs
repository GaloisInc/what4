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

import Data.Parameterized.NatRepr (NatRepr, knownNat, natValue, type (<=))
import Data.Parameterized.Some (Some(..))
import qualified Data.BitVector.Sized as BV
import Hedgehog (Gen)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import What4.BaseTypes (BaseBoolType, BaseBVType)
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
  }

-- | Default configuration: depth 5, widths 4/8/16
defaultGenConfig :: GenConfig
defaultGenConfig = GenConfig
  { gcMaxDepth = 5
  , gcBVWidths = [SomeWidth (knownNat @4), SomeWidth (knownNat @8), SomeWidth (knownNat @16)]
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

-- | Generate a leaf expression (constants/literals)
genLeaf :: GenConfig -> Gen (Some ExprBuilderAPI)
genLeaf cfg = Gen.frequency
  [ (1, genBoolLeaf)
  , (4, genBVLeaf cfg)
  ]

-- | Generate a non-leaf expression
genNode :: GenConfig -> Gen (Some ExprBuilderAPI)
genNode cfg = Gen.frequency
  [ (2, Some <$> genBoolNode cfg)
  , (8, genBVNode cfg)
  ]

-- | Generate a Boolean constant
genBoolLeaf :: Gen (Some ExprBuilderAPI)
genBoolLeaf = Gen.element
  [ Some TruePred
  , Some FalsePred
  ]

-- | Generate a BV literal with random width
genBVLeaf :: GenConfig -> Gen (Some ExprBuilderAPI)
genBVLeaf cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  Some <$> genBVLit w

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
  then genBoolConst
  else Gen.frequency
    [ (1, genBoolConst)
    , (4, Gen.scale (`div` 2) (genBoolNode cfg))
    ]

-- | Generate a Boolean constant
genBoolConst :: Gen (ExprBuilderAPI BaseBoolType)
genBoolConst = Gen.element [TruePred, FalsePred]

-- | Generate a Boolean expression node
genBoolNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBoolNode cfg = Gen.recursive Gen.choice
  [genBoolConst]
  [ do x <- genBool cfg
       pure $ NotPred x
  , do x <- genBool cfg
       y <- genBool cfg
       pure $ AndPred x y
  , do x <- genBool cfg
       y <- genBool cfg
       pure $ OrPred x y
  , do x <- genBool cfg
       y <- genBool cfg
       pure $ XorPred x y
  , do c <- genBool cfg
       t <- genBool cfg
       e <- genBool cfg
       pure $ ItePred c t e
  , genBVUltNode cfg
  , genBVSltNode cfg
  , genBVEqNode cfg
  ]

-- | Helpers to generate BV comparison operations
genBVUltNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBVUltNode cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  x <- genBVAtWidth cfg w
  y <- genBVAtWidth cfg w
  pure $ BVUlt x y

genBVSltNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBVSltNode cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  x <- genBVAtWidth cfg w
  y <- genBVAtWidth cfg w
  pure $ BVSlt x y

genBVEqNode :: GenConfig -> Gen (ExprBuilderAPI BaseBoolType)
genBVEqNode cfg = do
  SomeWidth w <- Gen.element (gcBVWidths cfg)
  x <- genBVAtWidth cfg w
  y <- genBVAtWidth cfg w
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
  then genBVLit w
  else Gen.frequency
    [ (1, genBVLit w)
    , (4, Gen.scale (`div` 2) (genBVNodeAtWidth cfg w))
    ]

-- | Generate a BV expression node at specific width
genBVNodeAtWidth :: forall w. (1 <= w) => GenConfig -> NatRepr w -> Gen (ExprBuilderAPI (BaseBVType w))
genBVNodeAtWidth cfg w = Gen.recursive Gen.choice
  [genBVLit w]
  [ do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVAdd x y
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVSub x y
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVMul x y
  , do x <- genBVAtWidth cfg w
       pure $ BVNeg x
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVAndBits x y
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVOrBits x y
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVXorBits x y
  , do x <- genBVAtWidth cfg w
       pure $ BVNotBits x
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVShl x y
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVLshr x y
  , do x <- genBVAtWidth cfg w
       y <- genBVAtWidth cfg w
       pure $ BVAshr x y
  , do c <- genBool cfg
       t <- genBVAtWidth cfg w
       e <- genBVAtWidth cfg w
       pure $ BVIte c t e
  ]
