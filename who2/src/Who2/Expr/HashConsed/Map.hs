{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Who2.Expr.HashConsed.Map
  ( ExprMap
  , eqBy2
  , ordBy2
  , empty
  , singleton
  , insert
  , insertWith
  , Who2.Expr.HashConsed.Map.lookup
  , delete
  , size
  , toList
  , fromList
  , union
  , unionWith
  , Who2.Expr.HashConsed.Map.map
  , mapWithKey
  , elems
  , keys
  ) where

import Data.Hashable (Hashable)
import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare), Eq2(liftEq2), Ord2(liftCompare2))
import qualified Data.IntMap.Strict as IM

import Who2.Expr (HasId(getId))

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | Map from elements with nonces to values, keyed by nonce indices.
newtype ExprMap k v = ExprMap (IM.IntMap (k, v))
  deriving (Hashable, Show)

eqBy2 ::
  (k1 -> k2 -> Bool) ->
  (v1 -> v2 -> Bool) ->
  ExprMap k1 v1 ->
  ExprMap k2 v2 ->
  Bool
eqBy2 eqK eqV (ExprMap x) (ExprMap y) =
  liftEq (\(k1, u) (k2, v) -> eqK k1 k2 && eqV u v) x y
{-# INLINE eqBy2 #-}

-- | Like 'liftCompare', but without typeclass constraints
ordBy2 ::
  (k1 -> k2 -> Ordering) ->
  (v1 -> v2 -> Ordering) ->
  ExprMap k1 v1 ->
  ExprMap k2 v2 ->
  Ordering
ordBy2 cmpK cmpV (ExprMap x) (ExprMap y) = liftCompare cmp' x y
  where cmp' (k1, v1) (k2, v2) =
          case cmpK k1 k2 of
            EQ -> cmpV v1 v2
            r -> r
{-# INLINE ordBy2 #-}

-- | @'eqBy2' (==) (==)@
instance (Eq k, Eq v) => Eq (ExprMap k v) where
  (==) = eqBy2 (==) (==)
  {-# INLINE (==) #-}

-- | @'ordBy2' 'compare' 'compare'@
instance (Ord k, Ord v) => Ord (ExprMap k v) where
  compare = ordBy2 compare compare
  {-# INLINE compare #-}

-- | @'eqBy2' (==)@
instance Eq k => Eq1 (ExprMap k) where
  liftEq eq = eqBy2 (==) eq
  {-# INLINE liftEq #-}

-- | @'eqBy2'@
instance Eq2 ExprMap where
  liftEq2 = eqBy2
  {-# INLINE liftEq2 #-}

-- | @'ordBy2' 'compare'@
instance Ord k => Ord1 (ExprMap k) where
  liftCompare cmp = ordBy2 compare cmp
  {-# INLINE liftCompare #-}

-- | @'ordBy2'@
instance Ord2 ExprMap where
  liftCompare2 = ordBy2
  {-# INLINE liftCompare2 #-}

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

empty :: ExprMap k v
empty = ExprMap IM.empty
{-# INLINE empty #-}

singleton :: HasId k => k -> v -> ExprMap k v
singleton expr val = ExprMap (IM.singleton (getId expr) (expr, val))
{-# INLINE singleton #-}

insert :: HasId k => k -> v -> ExprMap k v -> ExprMap k v
insert expr val (ExprMap m) = ExprMap (IM.insert (getId expr) (expr, val) m)
{-# INLINE insert #-}

insertWith :: HasId k => (v -> v -> v) -> k -> v -> ExprMap k v -> ExprMap k v
insertWith f expr val (ExprMap m) =
  ExprMap (IM.insertWith (\(_, v1) (e2, v2) -> (e2, f v1 v2)) (getId expr) (expr, val) m)
{-# INLINE insertWith #-}

lookup :: HasId k => k -> ExprMap k v -> Maybe v
lookup expr (ExprMap m) = snd <$> IM.lookup (getId expr) m
{-# INLINE lookup #-}

delete :: HasId k => k -> ExprMap k v -> ExprMap k v
delete expr (ExprMap m) = ExprMap (IM.delete (getId expr) m)
{-# INLINE delete #-}

size :: ExprMap k v -> Int
size (ExprMap m) = IM.size m
{-# INLINE size #-}

toList :: ExprMap k v -> [(k, v)]
toList (ExprMap m) = IM.elems m
{-# INLINE toList #-}

fromList :: HasId k => [(k, v)] -> ExprMap k v
fromList pairs = ExprMap (IM.fromList [(getId e, (e, v)) | (e, v) <- pairs])
{-# INLINE fromList #-}

union :: ExprMap k v -> ExprMap k v -> ExprMap k v
union (ExprMap m1) (ExprMap m2) = ExprMap (IM.union m1 m2)
{-# INLINE union #-}

unionWith :: (v -> v -> v) -> ExprMap k v -> ExprMap k v -> ExprMap k v
unionWith f (ExprMap m1) (ExprMap m2) =
  ExprMap (IM.unionWith (\(_, v1) (e2, v2) -> (e2, f v1 v2)) m1 m2)
{-# INLINE unionWith #-}

map :: (v -> w) -> ExprMap k v -> ExprMap k w
map f (ExprMap m) = ExprMap (IM.map (\(e, v) -> (e, f v)) m)
{-# INLINE map #-}

mapWithKey :: (k -> v -> w) -> ExprMap k v -> ExprMap k w
mapWithKey f (ExprMap m) = ExprMap (IM.map (\(e, v) -> (e, f e v)) m)
{-# INLINE mapWithKey #-}

elems :: ExprMap k v -> [v]
elems (ExprMap m) = [v | (_, v) <- IM.elems m]
{-# INLINE elems #-}

keys :: ExprMap k v -> [k]
keys (ExprMap m) = [e | (e, _) <- IM.elems m]
{-# INLINE keys #-}
