{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.Expr.HashConsed.ExprMap
  ( ExprMap
  , empty
  , singleton
  , insert
  , insertWith
  , lookup
  , delete
  , size
  , toList
  , fromList
  , union
  , unionWith
  , map
  , mapWithKey
  , elems
  , keys
  ) where

import Prelude hiding (lookup, map)
import qualified Data.IntMap.Strict as IM
import Data.Parameterized.Nonce (Nonce, indexValue)
import Data.Kind (Type)
import qualified What4.BaseTypes as BT

import Who2.Expr (HasNonce(getNonce))

-- | Map from elements with nonces to values, keyed by nonce indices.
newtype ExprMap (f :: BT.BaseType -> Type) (k :: BT.BaseType) (v :: Type) =
  ExprMap (IM.IntMap (f k, v))

-- | Internal helper: Convert nonce to Int key
nonceToKey :: forall k t (tp :: k). Nonce t tp -> Int
nonceToKey = fromIntegral . indexValue
{-# INLINE nonceToKey #-}

empty :: ExprMap f k v
empty = ExprMap IM.empty
{-# INLINE empty #-}

singleton :: HasNonce f => f k -> v -> ExprMap f k v
singleton expr val = ExprMap (IM.singleton (nonceToKey (getNonce expr)) (expr, val))
{-# INLINE singleton #-}

insert :: HasNonce f => f k -> v -> ExprMap f k v -> ExprMap f k v
insert expr val (ExprMap m) = ExprMap (IM.insert (nonceToKey (getNonce expr)) (expr, val) m)
{-# INLINE insert #-}

insertWith :: HasNonce f => (v -> v -> v) -> f k -> v -> ExprMap f k v -> ExprMap f k v
insertWith f expr val (ExprMap m) =
  ExprMap (IM.insertWith (\(_, v1) (e2, v2) -> (e2, f v1 v2)) (nonceToKey (getNonce expr)) (expr, val) m)
{-# INLINE insertWith #-}

lookup :: HasNonce f => f k -> ExprMap f k v -> Maybe v
lookup expr (ExprMap m) = snd <$> IM.lookup (nonceToKey (getNonce expr)) m
{-# INLINE lookup #-}

delete :: HasNonce f => f k -> ExprMap f k v -> ExprMap f k v
delete expr (ExprMap m) = ExprMap (IM.delete (nonceToKey (getNonce expr)) m)
{-# INLINE delete #-}

size :: ExprMap f k v -> Int
size (ExprMap m) = IM.size m
{-# INLINE size #-}

toList :: ExprMap f k v -> [(f k, v)]
toList (ExprMap m) = IM.elems m
{-# INLINE toList #-}

fromList :: HasNonce f => [(f k, v)] -> ExprMap f k v
fromList pairs = ExprMap (IM.fromList [(nonceToKey (getNonce e), (e, v)) | (e, v) <- pairs])
{-# INLINE fromList #-}

union :: ExprMap f k v -> ExprMap f k v -> ExprMap f k v
union (ExprMap m1) (ExprMap m2) = ExprMap (IM.union m1 m2)
{-# INLINE union #-}

unionWith :: (v -> v -> v) -> ExprMap f k v -> ExprMap f k v -> ExprMap f k v
unionWith f (ExprMap m1) (ExprMap m2) =
  ExprMap (IM.unionWith (\(_, v1) (e2, v2) -> (e2, f v1 v2)) m1 m2)
{-# INLINE unionWith #-}

map :: (v -> w) -> ExprMap f k v -> ExprMap f k w
map f (ExprMap m) = ExprMap (IM.map (\(e, v) -> (e, f v)) m)
{-# INLINE map #-}

mapWithKey :: (f k -> v -> w) -> ExprMap f k v -> ExprMap f k w
mapWithKey f (ExprMap m) = ExprMap (IM.map (\(e, v) -> (e, f e v)) m)
{-# INLINE mapWithKey #-}

elems :: ExprMap f k v -> [v]
elems (ExprMap m) = [v | (_, v) <- IM.elems m]
{-# INLINE elems #-}

keys :: ExprMap f k v -> [f k]
keys (ExprMap m) = [e | (e, _) <- IM.elems m]
{-# INLINE keys #-}
