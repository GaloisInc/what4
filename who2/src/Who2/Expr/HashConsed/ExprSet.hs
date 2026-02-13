{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

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
  , null
  ) where

import Prelude hiding (null)
import qualified Data.IntMap.Strict as IM
import Data.Parameterized.Nonce (Nonce, indexValue)
import Data.Kind (Type)
import qualified What4.BaseTypes as BT

import Who2.Expr (HasNonce(getNonce))

-- | Set of elements with nonces, keyed by nonce indices.
newtype ExprSet (f :: BT.BaseType -> Type) (tp :: BT.BaseType) =
  ExprSet (IM.IntMap (f tp))

-- | Internal helper: Convert nonce to Int key
nonceToKey :: forall k t (tp :: k). Nonce t tp -> Int
nonceToKey = fromIntegral . indexValue
{-# INLINE nonceToKey #-}

empty :: ExprSet f tp
empty = ExprSet IM.empty
{-# INLINE empty #-}

singleton :: HasNonce f => f tp -> ExprSet f tp
singleton e = ExprSet (IM.singleton (nonceToKey (getNonce e)) e)
{-# INLINE singleton #-}

insert :: HasNonce f => f tp -> ExprSet f tp -> ExprSet f tp
insert e (ExprSet m) = ExprSet (IM.insert (nonceToKey (getNonce e)) e m)
{-# INLINE insert #-}

member :: HasNonce f => f tp -> ExprSet f tp -> Bool
member e (ExprSet m) = IM.member (nonceToKey (getNonce e)) m
{-# INLINE member #-}

delete :: HasNonce f => f tp -> ExprSet f tp -> ExprSet f tp
delete e (ExprSet m) = ExprSet (IM.delete (nonceToKey (getNonce e)) m)
{-# INLINE delete #-}

size :: ExprSet f tp -> Int
size (ExprSet m) = IM.size m
{-# INLINE size #-}

toList :: ExprSet f tp -> [f tp]
toList (ExprSet m) = IM.elems m
{-# INLINE toList #-}

fromList :: HasNonce f => [f tp] -> ExprSet f tp
fromList es = ExprSet (IM.fromList [(nonceToKey (getNonce e), e) | e <- es])
{-# INLINE fromList #-}

union :: ExprSet f tp -> ExprSet f tp -> ExprSet f tp
union (ExprSet m1) (ExprSet m2) = ExprSet (IM.union m1 m2)
{-# INLINE union #-}

intersection :: ExprSet f tp -> ExprSet f tp -> ExprSet f tp
intersection (ExprSet m1) (ExprSet m2) = ExprSet (IM.intersection m1 m2)
{-# INLINE intersection #-}

difference :: ExprSet f tp -> ExprSet f tp -> ExprSet f tp
difference (ExprSet m1) (ExprSet m2) = ExprSet (IM.difference m1 m2)
{-# INLINE difference #-}

null :: ExprSet f tp -> Bool
null (ExprSet m) = IM.null m
{-# INLINE null #-}
