{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Who2.Laws.Helpers
  ( -- Equality helpers
    checkEqReflexivity
  , checkEqSymmetry
  , checkEqTransitivity
    -- Ordering helpers
  , checkOrdTransitivity
  , checkOrdFTransitivity
  , checkOrdAntisymmetry
  , checkOrdFAntisymmetry
  , checkOrdEqConsistency
    -- Mock types for testing
  , MockExpr(..)
  , MockExprBT(..)
  , genMockExprBT
  ) where

import Data.Hashable (Hashable(hashWithSalt))
import qualified Data.Parameterized.Classes as PC
import qualified What4.BaseTypes as BT
import qualified What4.Utils.AbstractDomains as AD
import Hedgehog (Gen)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Who2.Expr (HasId(getId))
import qualified Who2.Expr.Bloom.Polarized as PBS

-------------------------------------------------------------------------------
-- Equality Law Helpers
-------------------------------------------------------------------------------

-- | Check reflexivity property for equality relations
-- Given an equality function and a value, returns True if eq x x holds
checkEqReflexivity :: (a -> a -> Bool) -> a -> Bool
checkEqReflexivity eq x = eq x x

-- | Check symmetry property for equality relations
-- Given two equality functions (for both directions) and two values,
-- returns True if (x `eq` y) == (y `eq` x)
checkEqSymmetry :: (a -> b -> Bool) -> (b -> a -> Bool) -> a -> b -> Bool
checkEqSymmetry eqAB eqBA x y = eqAB x y == eqBA y x

-- | Check transitivity property for equality relations
-- Given three equality results (x == y, y == z, x == z), returns True if transitivity holds
-- That is: if x == y and y == z, then x == z must hold
checkEqTransitivity :: Bool -> Bool -> Bool -> Bool
checkEqTransitivity eqXY eqYZ eqXZ
  | eqXY && eqYZ = eqXZ  -- If x == y and y == z, then x == z must be True
  | otherwise = True     -- No constraint when precondition doesn't hold

-------------------------------------------------------------------------------
-- Ordering Law Helpers
-------------------------------------------------------------------------------

-- | Check transitivity property for ordering relations
-- Given three orderings (x `compare` y, y `compare` z, x `compare` z), returns True if transitivity holds
checkOrdTransitivity :: Ordering -> Ordering -> Ordering -> Bool
checkOrdTransitivity ord12 ord23 ord13 = case (ord12, ord23, ord13) of
  (LT, LT, LT) -> True
  (LT, LT, _) -> False
  (LT, EQ, LT) -> True
  (LT, EQ, _) -> False
  (EQ, LT, LT) -> True
  (EQ, LT, _) -> False
  (GT, GT, GT) -> True
  (GT, GT, _) -> False
  (GT, EQ, GT) -> True
  (GT, EQ, _) -> False
  (EQ, GT, GT) -> True
  (EQ, GT, _) -> False
  (EQ, EQ, EQ) -> True
  (EQ, EQ, _) -> False
  (LT, GT, _) -> True
  (GT, LT, _) -> True

-- | Check transitivity property for OrdF relations
-- Given three orderings (x `compareF` y, y `compareF` z, x `compareF` z), returns True if transitivity holds
checkOrdFTransitivity :: forall tp. PC.OrderingF tp tp -> PC.OrderingF tp tp -> PC.OrderingF tp tp -> Bool
checkOrdFTransitivity ord12 ord23 ord13 = case (ord12, ord23, ord13) of
  (PC.LTF, PC.LTF, PC.LTF) -> True
  (PC.LTF, PC.LTF, _) -> False
  (PC.LTF, PC.EQF, PC.LTF) -> True
  (PC.LTF, PC.EQF, _) -> False
  (PC.EQF, PC.LTF, PC.LTF) -> True
  (PC.EQF, PC.LTF, _) -> False
  (PC.GTF, PC.GTF, PC.GTF) -> True
  (PC.GTF, PC.GTF, _) -> False
  (PC.GTF, PC.EQF, PC.GTF) -> True
  (PC.GTF, PC.EQF, _) -> False
  (PC.EQF, PC.GTF, PC.GTF) -> True
  (PC.EQF, PC.GTF, _) -> False
  (PC.EQF, PC.EQF, PC.EQF) -> True
  (PC.EQF, PC.EQF, _) -> False
  (PC.LTF, PC.GTF, _) -> True
  (PC.GTF, PC.LTF, _) -> True

-- | Check antisymmetry property for ordering relations
-- Given two orderings (x `compare` y, y `compare` x), returns True if antisymmetry holds
checkOrdAntisymmetry :: Ordering -> Ordering -> Bool
checkOrdAntisymmetry ord12 ord21 = case (ord12, ord21) of
  (LT, GT) -> True
  (EQ, EQ) -> True
  (GT, LT) -> True
  _ -> False

-- | Check antisymmetry property for OrdF relations
-- Given two orderings (x `compareF` y, y `compareF` x), returns True if antisymmetry holds
checkOrdFAntisymmetry :: forall tp. PC.OrderingF tp tp -> PC.OrderingF tp tp -> Bool
checkOrdFAntisymmetry ord12 ord21 = case (ord12, ord21) of
  (PC.LTF, PC.GTF) -> True
  (PC.EQF, PC.EQF) -> True
  (PC.GTF, PC.LTF) -> True
  _ -> False

-- | Check consistency between Eq and Ord
-- Given an equality result and a comparison result, returns True if they are consistent
-- That is: (x == y) if and only if (compare x y == EQ)
checkOrdEqConsistency :: Bool -> Ordering -> Bool
checkOrdEqConsistency isEq ord = case (isEq, ord) of
  (True, EQ) -> True    -- Equal values must compare as EQ
  (False, EQ) -> False  -- Non-equal values cannot compare as EQ
  (True, _) -> False    -- Equal values cannot compare as LT or GT
  (False, _) -> True    -- Non-equal values can compare as LT or GT

-------------------------------------------------------------------------------
-- Mock Types for Testing
-------------------------------------------------------------------------------

-- | Mock expression type for testing non-parameterized data structures
data MockExpr = MockExpr Int
  deriving (Eq, Ord, Show)

instance HasId MockExpr where
  getId (MockExpr i) = i

instance Hashable MockExpr where
  hashWithSalt s (MockExpr i) = s `hashWithSalt` i

instance PBS.Polarizable MockExpr where
  polarity (MockExpr x)
    | x < 0 = PBS.Negative (MockExpr (negate x))
    | otherwise = PBS.Positive (MockExpr x)

-- | Mock expression type for testing BaseType-parameterized data structures
data MockExprBT (tp :: BT.BaseType) = MockExprBT Int (BT.BaseTypeRepr tp)

instance Eq (MockExprBT tp) where
  MockExprBT i _ == MockExprBT j _ = i == j

instance Ord (MockExprBT tp) where
  compare (MockExprBT i _) (MockExprBT j _) = compare i j

instance Show (MockExprBT tp) where
  show (MockExprBT i _) = "MockExprBT " ++ show i

instance HasId (MockExprBT tp) where
  getId (MockExprBT i _) = i

instance Hashable (MockExprBT tp) where
  hashWithSalt s (MockExprBT i _) = s `hashWithSalt` i

instance AD.HasAbsValue MockExprBT where
  getAbsValue (MockExprBT _ repr) = AD.avTop repr

-------------------------------------------------------------------------------
-- Mock Generator Helpers
-------------------------------------------------------------------------------

-- | Generate a MockExprBT for a specific BaseType using TypeApplications.
--
-- Example usage:
--   @genMockExprBT \@(BT.BaseBVType 8)@
genMockExprBT :: forall tp. PC.KnownRepr BT.BaseTypeRepr tp => Gen (MockExprBT tp)
genMockExprBT = MockExprBT <$> Gen.int (Range.linear 0 100) <*> pure PC.knownRepr
