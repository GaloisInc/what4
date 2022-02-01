{-|
Module      : What4.SemiRing
Description : Definitions related to semiring structures over base types.
Copyright   : (c) Galois Inc, 2019-2020
License     : BSD3
Maintainer  : rdockins@galois.com

The algebraic assumptions we make about our semirings are that:

* addition is commutative and associative, with a unit called zero,
* multiplication is commutative and associative, with a unit called one,
* one and zero are distinct values,
* multiplication distributes through addition, and
* multiplication by zero gives zero.

Note that we do not assume the existence of additive inverses (hence,
semirings), but we do assume commutativity of multiplication.

Note, moreover, that bitvectors can be equipped with two different
semirings (the usual arithmetic one and the XOR/AND boolean ring imposed
by the boolean algebra structure), which occasionally requires some care.

In addition, some semirings are "ordered" semirings.  These are equipped
with a total ordering relation such that addition is both order-preserving
and order-reflecting; that is, @x <= y@ iff @x + z <= y + z@.
Moreover ordered semirings satisfy: @0 <= x@ and @0 <= y@ implies @0 <= x*y@.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.SemiRing
  ( -- * Semiring datakinds
    type SemiRing
  , type SemiRingInteger
  , type SemiRingReal
  , type SemiRingBV
  , type BVFlavor
  , type BVBits
  , type BVArith

    -- * Semiring representations
  , SemiRingRepr(..)
  , OrderedSemiRingRepr(..)
  , BVFlavorRepr(..)
  , SemiRingBase
  , semiRingBase
  , orderedSemiRing

    -- * Semiring coefficients
  , Coefficient
  , zero
  , one
  , add
  , mul
  , eq
  , le
  , lt
  , sr_compare
  , sr_hashWithSalt

    -- * Semiring product occurrences
  , Occurrence
  , occ_add
  , occ_one
  , occ_eq
  , occ_hashWithSalt
  , occ_compare
  , occ_count
  ) where

import GHC.TypeNats (Nat)
import qualified Data.BitVector.Sized as BV
import Data.Kind
import Data.Hashable
import Data.Parameterized.Classes
import Data.Parameterized.TH.GADT
import Numeric.Natural (Natural)

import What4.BaseTypes

-- | Data-kind indicating the two flavors of bitvector semirings.
--   The ordinary arithmetic semiring consists of addition and multiplication,
--   and the "bits" semiring consists of bitwise xor and bitwise and.
data BVFlavor = BVArith | BVBits

-- | Data-kind representing the semirings What4 supports.
data SemiRing
  = SemiRingInteger
  | SemiRingReal
  | SemiRingBV BVFlavor Nat

type BVArith = 'BVArith    -- ^ @:: 'BVFlavor'@
type BVBits  = 'BVBits     -- ^ @:: 'BVFlavor'@

type SemiRingInteger = 'SemiRingInteger   -- ^ @:: 'SemiRing'@
type SemiRingReal = 'SemiRingReal         -- ^ @:: 'SemiRing'@
type SemiRingBV = 'SemiRingBV             -- ^ @:: 'BVFlavor' -> 'Nat' -> 'SemiRing'@

data BVFlavorRepr (fv :: BVFlavor) where
  BVArithRepr :: BVFlavorRepr BVArith
  BVBitsRepr  :: BVFlavorRepr BVBits

data SemiRingRepr (sr :: SemiRing) where
  SemiRingIntegerRepr :: SemiRingRepr SemiRingInteger
  SemiRingRealRepr    :: SemiRingRepr SemiRingReal
  SemiRingBVRepr      :: (1 <= w) => !(BVFlavorRepr fv) -> !(NatRepr w) -> SemiRingRepr (SemiRingBV fv w)

-- | The subset of semirings that are equipped with an appropriate (order-respecting) total order.
data OrderedSemiRingRepr (sr :: SemiRing) where
  OrderedSemiRingIntegerRepr :: OrderedSemiRingRepr SemiRingInteger
  OrderedSemiRingRealRepr    :: OrderedSemiRingRepr SemiRingReal

-- | Compute the base type of the given semiring.
semiRingBase :: SemiRingRepr sr -> BaseTypeRepr (SemiRingBase sr)
semiRingBase SemiRingIntegerRepr = BaseIntegerRepr
semiRingBase SemiRingRealRepr    = BaseRealRepr
semiRingBase (SemiRingBVRepr _fv w)  = BaseBVRepr w

-- | Compute the semiring corresponding to the given ordered semiring.
orderedSemiRing :: OrderedSemiRingRepr sr -> SemiRingRepr sr
orderedSemiRing OrderedSemiRingIntegerRepr = SemiRingIntegerRepr
orderedSemiRing OrderedSemiRingRealRepr    = SemiRingRealRepr

type family SemiRingBase (sr :: SemiRing) :: BaseType where
  SemiRingBase SemiRingInteger   = BaseIntegerType
  SemiRingBase SemiRingReal      = BaseRealType
  SemiRingBase (SemiRingBV fv w) = BaseBVType w

-- | The constant values in the semiring.
type family Coefficient (sr :: SemiRing) :: Type where
  Coefficient SemiRingInteger    = Integer
  Coefficient SemiRingReal       = Rational
  Coefficient (SemiRingBV fv w)  = BV.BV w

-- | The 'Occurrence' family counts how many times a term occurs in a
--   product. For most semirings, this is just a natural number
--   representing the exponent. For the boolean ring of bitvectors,
--   however, it is unit because the lattice operations are
--   idempotent.
type family Occurrence (sr :: SemiRing) :: Type where
  Occurrence SemiRingInteger        = Natural
  Occurrence SemiRingReal           = Natural
  Occurrence (SemiRingBV BVArith w) = Natural
  Occurrence (SemiRingBV BVBits w)  = ()

sr_compare :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Ordering
sr_compare SemiRingIntegerRepr  = compare
sr_compare SemiRingRealRepr     = compare
sr_compare (SemiRingBVRepr _ _) = compare

sr_hashWithSalt :: SemiRingRepr sr -> Int -> Coefficient sr -> Int
sr_hashWithSalt SemiRingIntegerRepr  = hashWithSalt
sr_hashWithSalt SemiRingRealRepr     = hashWithSalt
sr_hashWithSalt (SemiRingBVRepr _ _) = hashWithSalt

occ_one :: SemiRingRepr sr -> Occurrence sr
occ_one SemiRingIntegerRepr = 1
occ_one SemiRingRealRepr    = 1
occ_one (SemiRingBVRepr BVArithRepr _) = 1
occ_one (SemiRingBVRepr BVBitsRepr _)  = ()

occ_add :: SemiRingRepr sr -> Occurrence sr -> Occurrence sr -> Occurrence sr
occ_add SemiRingIntegerRepr = (+)
occ_add SemiRingRealRepr    = (+)
occ_add (SemiRingBVRepr BVArithRepr _) = (+)
occ_add (SemiRingBVRepr BVBitsRepr _)  = \_ _ -> ()

occ_count :: SemiRingRepr sr -> Occurrence sr -> Natural
occ_count SemiRingIntegerRepr = id
occ_count SemiRingRealRepr    = id
occ_count (SemiRingBVRepr BVArithRepr _) = id
occ_count (SemiRingBVRepr BVBitsRepr _)  = \_ -> 1

occ_eq :: SemiRingRepr sr -> Occurrence sr -> Occurrence sr -> Bool
occ_eq SemiRingIntegerRepr = (==)
occ_eq SemiRingRealRepr    = (==)
occ_eq (SemiRingBVRepr BVArithRepr _) = (==)
occ_eq (SemiRingBVRepr BVBitsRepr _)  = \_ _ -> True

occ_hashWithSalt :: SemiRingRepr sr -> Int -> Occurrence sr -> Int
occ_hashWithSalt SemiRingIntegerRepr  = hashWithSalt
occ_hashWithSalt SemiRingRealRepr     = hashWithSalt
occ_hashWithSalt (SemiRingBVRepr BVArithRepr _) = hashWithSalt
occ_hashWithSalt (SemiRingBVRepr BVBitsRepr _) = hashWithSalt

occ_compare :: SemiRingRepr sr -> Occurrence sr -> Occurrence sr -> Ordering
occ_compare SemiRingIntegerRepr  = compare
occ_compare SemiRingRealRepr     = compare
occ_compare (SemiRingBVRepr BVArithRepr _) = compare
occ_compare (SemiRingBVRepr BVBitsRepr _)  = compare

zero :: SemiRingRepr sr -> Coefficient sr
zero SemiRingIntegerRepr      = 0 :: Integer
zero SemiRingRealRepr         = 0 :: Rational
zero (SemiRingBVRepr BVArithRepr w) = BV.zero w
zero (SemiRingBVRepr BVBitsRepr w)  = BV.zero w

one :: SemiRingRepr sr -> Coefficient sr
one SemiRingIntegerRepr          = 1 :: Integer
one SemiRingRealRepr             = 1 :: Rational
one (SemiRingBVRepr BVArithRepr w) = BV.mkBV w 1
one (SemiRingBVRepr BVBitsRepr w)  = BV.maxUnsigned w

add :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Coefficient sr
add SemiRingIntegerRepr      = (+)
add SemiRingRealRepr         = (+)
add (SemiRingBVRepr BVArithRepr w) = BV.add w
add (SemiRingBVRepr BVBitsRepr _)  = BV.xor

mul :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Coefficient sr
mul SemiRingIntegerRepr      = (*)
mul SemiRingRealRepr         = (*)
mul (SemiRingBVRepr BVArithRepr w) = BV.mul w
mul (SemiRingBVRepr BVBitsRepr _)  = BV.and

eq :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Bool
eq SemiRingIntegerRepr      = (==)
eq SemiRingRealRepr         = (==)
eq (SemiRingBVRepr _ _)     = (==)

le :: OrderedSemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Bool
le OrderedSemiRingIntegerRepr = (<=)
le OrderedSemiRingRealRepr    = (<=)

lt :: OrderedSemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Bool
lt OrderedSemiRingIntegerRepr = (<)
lt OrderedSemiRingRealRepr    = (<)

$(return [])

instance TestEquality BVFlavorRepr where
  testEquality = $(structuralTypeEquality [t|BVFlavorRepr|] [])
instance Eq (BVFlavorRepr fv) where
  x == y = isJust (testEquality x y)

instance TestEquality OrderedSemiRingRepr where
  testEquality = $(structuralTypeEquality [t|OrderedSemiRingRepr|] [])
instance Eq (OrderedSemiRingRepr sr) where
  x == y = isJust (testEquality x y)

instance TestEquality SemiRingRepr where
  testEquality =
    $(structuralTypeEquality [t|SemiRingRepr|]
      [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|testEquality|])
      , (ConType [t|BVFlavorRepr|] `TypeApp` AnyType, [|testEquality|])
      ])
instance Eq (SemiRingRepr sr) where
  x == y = isJust (testEquality x y)

instance OrdF BVFlavorRepr where
  compareF = $(structuralTypeOrd [t|BVFlavorRepr|] [])

instance OrdF OrderedSemiRingRepr where
  compareF = $(structuralTypeOrd [t|OrderedSemiRingRepr|] [])

instance OrdF SemiRingRepr where
  compareF =
    $(structuralTypeOrd [t|SemiRingRepr|]
      [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|compareF|])
      , (ConType [t|BVFlavorRepr|] `TypeApp` AnyType, [|compareF|])
      ])

instance HashableF BVFlavorRepr where
  hashWithSaltF = $(structuralHashWithSalt [t|BVFlavorRepr|] [])
instance Hashable (BVFlavorRepr fv) where
  hashWithSalt = hashWithSaltF

instance HashableF OrderedSemiRingRepr where
  hashWithSaltF = $(structuralHashWithSalt [t|OrderedSemiRingRepr|] [])
instance Hashable (OrderedSemiRingRepr sr) where
  hashWithSalt = hashWithSaltF

instance HashableF SemiRingRepr where
  hashWithSaltF = $(structuralHashWithSalt [t|SemiRingRepr|] [])
instance Hashable (SemiRingRepr sr) where
  hashWithSalt = hashWithSaltF
