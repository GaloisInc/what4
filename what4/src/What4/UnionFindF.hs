{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
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
  , singletonKeySet
  , insertKeySet
  , memberKeySet
  , unionKeySet
  , keySetToList
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
  , Equation(..)
  , basis
    -- ** Modifications
  , insert
  , unionByKey
  , unionByValue
  , mapAnn
  , traverseUnionFind
  ) where

import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Maybe (isJust)
import Data.Parameterized.Classes (EqF(eqF), OrdF(compareF), toOrdering)
import Data.Type.Equality (TestEquality, testEquality)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import What4.UnionFind qualified as UF
import What4.UnionFind (UnionFindName)
import Data.Parameterized.Some (Some (Some))

---------------------------------------------------------------------
-- Key

-- This does not need an @f@ parameter because it is determined by @u@
newtype Key u x = Key { getKey :: UF.Key u }
  deriving Eq

keyValue :: Key u x -> Int
keyValue = UF.keyValue . getKey
{-# INLINE keyValue #-}

---------------------------------------------------------------------
-- KeySet

type KeySet :: UnionFindName -> Type
newtype KeySet u = KeySet { getKeySet :: UF.KeySet u }
  deriving (Eq, Ord, Semigroup, Show)

emptyKeySet :: KeySet u
emptyKeySet = KeySet UF.emptyKeySet

singletonKeySet :: Key u x -> KeySet u
singletonKeySet = coerce UF.singletonKeySet

insertKeySet :: Key u x -> KeySet u -> KeySet u
insertKeySet = coerce UF.insertKeySet

memberKeySet :: Key u x -> KeySet u -> Bool
memberKeySet = coerce UF.memberKeySet

unionKeySet :: KeySet u -> KeySet u -> KeySet u
unionKeySet = coerce UF.unionKeySet

keySetToList :: KeySet u -> [Some (Key u)]
keySetToList = map (Some . Key) . UF.keySetToList . getKeySet

---------------------------------------------------------------------
-- AnyF (internal details)

newtype AnyF f = AnyF { _getAnyF :: f Any }

toAny :: f x -> AnyF f
toAny = unsafeCoerce
{-# INLINE toAny #-}

unsafeFromAny :: AnyF f -> f x
unsafeFromAny = unsafeCoerce
{-# INLINE unsafeFromAny #-}

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

instance (Eq ann, TestEquality f) => Eq (UnionFind u ann f) where
  UnionFind uf == UnionFind uf' =
    UF.ufLiftEq2 (==) (\(AnyF f) (AnyF f') -> isJust (testEquality f f')) uf uf'

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
     -- see invariant on 'UnionFind'
     fmap unsafeFromAny (UF.findValue f)
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

data Equation ann f
  = forall x. Equation { eqLhs :: UF.Annotated ann (f x), eqRhs :: f x }

-- | Return a set of equations that is sufficient to generate the rest via
-- reflexive-symmetric-transitive closure.
basis ::
  EqF f =>
  OrdF f =>
  UnionFind u ann f ->
  (UnionFind u ann f, [Equation ann f])
basis (UnionFind u) =
  let (u', eqs) = UF.basis u in
  (UnionFind u', map (uncurry mkEq) eqs)
  where
    mkEq (UF.Annotated ann root) val =
      -- see invariant on 'UnionFind'
      Equation (UF.Annotated ann (unsafeFromAny root)) (unsafeFromAny val)

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
  (UnionFind u ann f, Find u ann f x)
unionByKey (UnionFind u) (Key k1) (Key k2) =
  let (u', r) = UF.unionByKey u k1 k2 in
  (UnionFind u', unsafeCoerceFind r)
{-# INLINE unionByKey #-}

unionByValue ::
  EqF f =>
  OrdF f =>
  Semigroup ann =>
  UnionFind u ann f ->
  UF.Annotated ann (f x) ->
  UF.Annotated ann (f x) ->
  (UnionFind u ann f, Find u ann f x)
unionByValue (UnionFind u) v1 v2 =
  let (u', r) = UF.unionByValue u (toAny <$> v1) (toAny <$> v2) in
  (UnionFind u', unsafeCoerceFind r)
{-# INLINE unionByValue #-}

mapAnn ::
  forall u f ann ann'.
  (EqF f, OrdF f) =>
  (ann -> ann') ->
  UnionFind u ann f ->
  UnionFind u ann' f
mapAnn =
  coerce
    @((ann -> ann') -> UF.UnionFind u ann (AnyF f) -> UF.UnionFind u ann' (AnyF f))
    @((ann -> ann') -> UnionFind u ann f -> UnionFind u ann' f)
    UF.mapAnn
{-# INLINE mapAnn #-}

traverseUnionFind ::
  Applicative m =>
  EqF g =>
  OrdF g =>
  (forall x. f x -> m (g x)) ->
  UnionFind u ann f ->
  m (UnionFind u ann g)
traverseUnionFind f (UnionFind u) =
  UnionFind <$> UF.traverseUnionFind (\(AnyF x) -> AnyF <$> f x) u
