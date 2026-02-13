{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.Laws.Helpers
  ( checkOrdTransitivity
  , checkOrdFTransitivity
  , checkOrdAntisymmetry
  , checkOrdFAntisymmetry
  ) where

import qualified Data.Parameterized.Classes as PC

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
