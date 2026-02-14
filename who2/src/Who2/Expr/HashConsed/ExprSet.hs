{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Who2.Expr.HashConsed.ExprSet
  ( ExprSet
  , empty
  , singleton
  , insert
  , member
  , delete
  , size
  , toList
  , fromList
  , union
  , intersection
  , difference
  , Who2.Expr.HashConsed.ExprSet.null
  ) where

import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IM

import Who2.Expr (HasId(getId))

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | Set of elements with nonces, keyed by nonce indices.
newtype ExprSet a = ExprSet (IM.IntMap a)
  deriving (Hashable, Show)

-- | By keys only, safe due to hash-consing
eq :: ExprSet a -> ExprSet b -> Bool
eq (ExprSet x) (ExprSet y) = IM.keys x == IM.keys y
{-# INLINE eq #-}

-- | By keys only, safe due to hash-consing
instance Eq (ExprSet a) where
  (==) = eq
  {-# INLINE (==) #-}

-- | By keys only, safe due to hash-consing
cmp :: ExprSet a -> ExprSet b -> Ordering
cmp (ExprSet x) (ExprSet y) = compare (IM.keys x) (IM.keys y)
{-# INLINE cmp #-}

-- | By keys only, safe due to hash-consing
instance Ord (ExprSet a) where
  compare = cmp
  {-# INLINE compare #-}

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

empty :: ExprSet a
empty = ExprSet IM.empty
{-# INLINE empty #-}

singleton :: HasId a => a -> ExprSet a
singleton e = ExprSet (IM.singleton (getId e) e)
{-# INLINE singleton #-}

insert :: HasId a => a -> ExprSet a -> ExprSet a
insert e (ExprSet m) = ExprSet (IM.insert (getId e) e m)
{-# INLINE insert #-}

member :: HasId a => a -> ExprSet a -> Bool
member e (ExprSet m) = IM.member (getId e) m
{-# INLINE member #-}

delete :: HasId a => a -> ExprSet a -> ExprSet a
delete e (ExprSet m) = ExprSet (IM.delete (getId e) m)
{-# INLINE delete #-}

size :: ExprSet a -> Int
size (ExprSet m) = IM.size m
{-# INLINE size #-}

toList :: ExprSet a -> [a]
toList (ExprSet m) = IM.elems m
{-# INLINE toList #-}

fromList :: HasId a => [a] -> ExprSet a
fromList es = ExprSet (IM.fromList [(getId e, e) | e <- es])
{-# INLINE fromList #-}

union :: ExprSet a -> ExprSet a -> ExprSet a
union (ExprSet m1) (ExprSet m2) = ExprSet (IM.union m1 m2)
{-# INLINE union #-}

intersection :: ExprSet a -> ExprSet a -> ExprSet a
intersection (ExprSet m1) (ExprSet m2) = ExprSet (IM.intersection m1 m2)
{-# INLINE intersection #-}

difference :: ExprSet a -> ExprSet a -> ExprSet a
difference (ExprSet m1) (ExprSet m2) = ExprSet (IM.difference m1 m2)
{-# INLINE difference #-}

null :: ExprSet a -> Bool
null (ExprSet m) = IM.null m
{-# INLINE null #-}
