{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}

module What4.UnionFindF
  ( -- * 'Key'
    Key
  , keyValue
    -- ** 'KeySet'
  , KeySet
  , emptyKeySet
  , insertKeySet
  , memberKeySet
  , unionKeySet
    -- * 'UnionFindF'
  , UnionFind
  , SomeUnionFind(..)
  , empty
    -- ** Queries
  , UF.Annotated(..)
  , Find
  , findKey
  , findUnionFind
  , findValue
  , findByKey
  , findByValue
    -- ** Modifications
  , insert
  , unionByKey
  , unionByValue
  ) where

import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Parameterized.Classes (EqF(eqF), OrdF(compareF), toOrdering)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import What4.UnionFind qualified as UF
import What4.UnionFind (UnionFindName)

---------------------------------------------------------------------
-- Key

-- This does not need an @f@ parameter because it is determined by @u@
newtype Key u x = Key { getKey :: UF.Key u }

keyValue :: Key u x -> Int
keyValue = UF.keyValue . getKey
{-# INLINE keyValue #-}

---------------------------------------------------------------------
-- KeySet

type KeySet :: UnionFindName -> Type
newtype KeySet u = KeySet { _getKeySet :: UF.KeySet u }
  deriving (Eq, Ord, Semigroup, Show)

emptyKeySet :: KeySet u
emptyKeySet = KeySet UF.emptyKeySet

insertKeySet :: Key u x -> KeySet u -> KeySet u
insertKeySet = coerce UF.insertKeySet

memberKeySet :: Key u x -> KeySet u -> Bool
memberKeySet = coerce UF.memberKeySet

unionKeySet :: KeySet u -> KeySet u -> KeySet u
unionKeySet = coerce UF.unionKeySet

---------------------------------------------------------------------
-- AnyF (internal details)

newtype AnyF f = AnyF { getAnyF :: f Any }

toAny :: f x -> AnyF f
toAny = unsafeCoerce
{-# INLINE toAny #-}

instance EqF f => Eq (AnyF f) where
  AnyF f == AnyF g = eqF f g
  {-# INLINE (==) #-}

instance (EqF f, OrdF f) => Ord (AnyF f) where
  compare (AnyF f) (AnyF g) = toOrdering (compareF f g)
  {-# INLINE compare #-}

---------------------------------------------------------------------
-- UnionFind

type UnionFind :: UnionFindName -> Type -> (l -> Type) -> Type
newtype UnionFind u ann f
  = UnionFind
    -- Invariant: Every @'Key' u x@ transitively points to value of type @f x@.
    -- In particular, every equivalence class only contains values of a single
    -- type @x@.
    --
    -- Let's argue inductively over sequences of API calls.
    --
    -- - 'empty': There are no keys nor classes.
    -- - 'insert': The returned key points to the provided value of type @f x@.
    -- - 'findBy*': If the invariant held before, then it is maintained by path
    --   compression, as paths are compressed within an equivalence class.
    -- - 'unionBy{Key,Value}': These methods require the types of the
    --   {keys,values} to match, thus upholding the invariant when the classes
    --   are merged.
    { _getUnionFind :: UF.UnionFind u ann (AnyF f) }

data SomeUnionFind ann f = forall u. SomeUnionFind (UnionFind u ann f)

empty :: SomeUnionFind ann f
empty =
  case UF.empty of
    UF.SomeUnionFind uf -> SomeUnionFind (UnionFind uf)

type Find :: UnionFindName -> Type -> (l -> Type) -> l -> Type
data Find u ann f x
  = Find
    { -- | The 'Key' of the root node. Guaranteed to be present in @u@.
      findKey :: Key u x
      -- | The possibly-modified union-find
    , findUnionFind :: UnionFind u ann f
      -- | The value of the root note and its annotation
    , findValue :: UF.Annotated ann (f x)
    }

-- | Not exported, caller must ensure the @AnyF@ is of type @x@
unsafeCoerceFind ::
  forall u ann f x.
  UF.Find u ann (AnyF f) ->
  Find u ann f x
unsafeCoerceFind f =
  Find
  { findKey = Key (UF.findKey f)
  , findUnionFind = UnionFind (UF.findUnionFind f)
  , findValue =
      unsafeCoerce  -- see invariant on 'UnionFind'
        @(UF.Annotated ann (f Any))
        @(UF.Annotated ann (f x))
        (fmap getAnyF (UF.findValue f))
  }

findByKey ::
  EqF f =>
  OrdF f =>
  UnionFind u ann f ->
  Key u x ->
  Find u ann f x
findByKey (UnionFind u) (Key k) = unsafeCoerceFind (UF.findByKey u k)

findByValue ::
  EqF f =>
  OrdF f =>
  UnionFind u ann f ->
  f x ->
  Maybe (Find u ann f x)
findByValue (UnionFind u) v = unsafeCoerceFind <$> UF.findByValue u (toAny v)

insert ::
  EqF f =>
  OrdF f =>
  Semigroup ann =>
  UnionFind u ann f ->
  f x ->
  ann ->
  Find u ann f x
insert (UnionFind u) val ann = unsafeCoerceFind (UF.insert u (toAny val) ann)

unionByKey ::
  EqF f =>
  OrdF f =>
  Semigroup ann =>
  UnionFind u ann f ->
  Key u x ->
  Key u x ->
  UnionFind u ann f
unionByKey (UnionFind u) (Key k1) (Key k2) =
  UnionFind (UF.unionByKey u k1 k2)
{-# INLINE unionByKey #-}

unionByValue ::
  EqF f =>
  OrdF f =>
  Semigroup ann =>
  UnionFind u ann f ->
  UF.Annotated ann (f x) ->
  UF.Annotated ann (f x) ->
  UnionFind u ann f
unionByValue (UnionFind u) v1 v2 =
  UnionFind (UF.unionByValue u (toAny <$> v1) (toAny <$> v2))
{-# INLINE unionByValue #-}
