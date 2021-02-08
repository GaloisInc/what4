{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module What4.IndexLit where

import qualified Data.BitVector.Sized as BV
import Data.Parameterized.Classes

import What4.BaseTypes

------------------------------------------------------------------------
-- IndexLit

-- | This represents a concrete index value, and is used for creating
-- arrays.
data IndexLit idx where
  IntIndexLit :: !Integer -> IndexLit BaseIntegerType
  BVIndexLit :: (1 <= w) => !(NatRepr w) -> !(BV.BV w) ->  IndexLit (BaseBVType w)

instance Eq (IndexLit tp) where
  x == y = isJust (testEquality x y)

instance TestEquality IndexLit where
  testEquality (IntIndexLit x) (IntIndexLit y) =
    if x == y then
     Just Refl
     else
     Nothing
  testEquality (BVIndexLit wx x) (BVIndexLit wy y) = do
    Refl <- testEquality wx wy
    if x == y then Just Refl else Nothing
  testEquality _ _ =
    Nothing

instance OrdF IndexLit where
  compareF (IntIndexLit x) (IntIndexLit y) = fromOrdering (compare x y)
  compareF IntIndexLit{} _ = LTF
  compareF _ IntIndexLit{} = GTF
  compareF (BVIndexLit wx x) (BVIndexLit wy y) =
    case compareF wx wy of
      LTF -> LTF
      GTF -> GTF
      EQF -> fromOrdering (compare x y)

instance Hashable (IndexLit tp) where
  hashWithSalt = hashIndexLit
  {-# INLINE hashWithSalt #-}


hashIndexLit :: Int -> IndexLit idx -> Int
s `hashIndexLit` (IntIndexLit i) =
    s `hashWithSalt` (0::Int)
      `hashWithSalt` i
s `hashIndexLit` (BVIndexLit w i) =
    s `hashWithSalt` (1::Int)
      `hashWithSalt` w
      `hashWithSalt` i

instance HashableF IndexLit where
  hashWithSaltF = hashIndexLit

instance Show (IndexLit tp) where
  showsPrec p (IntIndexLit i) s = showsPrec p i s
  showsPrec p (BVIndexLit w i) s = showsPrec p i ("::[" ++ shows w (']' : s))

instance ShowF IndexLit
