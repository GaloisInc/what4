{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}

-- | See "What4.ExprEqualities".
module What4.UnionFind
  ( -- * 'UnionFindName'
    UnionFindName
  , -- * 'Key'
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
    -- * 'UnionFind'
  , UnionFind
  , SomeUnionFind(..)
  , empty
  , ufLiftEq2
    -- ** Queries
  , Annotated(..)
  , Find
  , findKey
  , findUnionFind
  , findValue
  , findByKey
  , findByValue
  , equal
  , basis
    -- ** Modifications
  , insert
  , unionByKey
  , unionByValue
  , mapAnn
  , traverseUnionFind
  ) where

import Control.Lens.Indexed qualified as Ixd
import Data.Bifunctor (Bifunctor(bimap), first)
import Data.Coerce (coerce)
import Data.Functor.Classes (Eq1(liftEq), Eq2(liftEq2))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Monoid (Sum(Sum))
import Data.Traversable (foldMapDefault)

---------------------------------------------------------------------
-- UnionFindName

-- | Kind of type-level names for 'UnionFind's.
--
-- In particular, the kind of the type variable @u@ on 'UnionFind'.
--
-- Only made available to clients via existential quantification, so that any
-- two variables of this kind are treated as distinct by GHC. To maintain this
-- invariant, no constructor is exported.
data UnionFindName

---------------------------------------------------------------------
-- Key

-- | Keys are tagged with @u@, the type-level name of the union-find.
type Key :: UnionFindName -> Type
newtype Key u = Key { keyValue :: Int }
  deriving (Eq, Show)

---------------------------------------------------------------------
-- KeySet

-- | A set of 'Key's.
--
-- Just a @newtype@ around 'IntSet', so should be quite fast.
type KeySet :: UnionFindName -> Type
newtype KeySet u = KeySet { _getKeySet :: IntSet }
  deriving (Eq, Ord, Semigroup, Show)

emptyKeySet :: KeySet u
emptyKeySet = KeySet IntSet.empty

singletonKeySet :: Key u -> KeySet u
singletonKeySet = coerce IntSet.singleton

insertKeySet :: Key u -> KeySet u -> KeySet u
insertKeySet = coerce IntSet.insert

memberKeySet :: Key u -> KeySet u -> Bool
memberKeySet = coerce IntSet.member

unionKeySet :: KeySet u -> KeySet u -> KeySet u
unionKeySet = coerce IntSet.union

keySetToList :: KeySet u -> [Key u]
keySetToList = coerce IntSet.toList

---------------------------------------------------------------------
-- KeyMap

-- | A map from 'Key's to @a@s.
--
-- Does not guarantee that every 'Key' from @u@ is present, i.e., 'lookupKeyMap'
-- is partial (returns 'Maybe').
--
-- Just a @newtype@ around 'IntSet', so should be quite fast.
type KeyMap :: UnionFindName -> Type -> Type
newtype KeyMap u a = KeyMap { getKeyMap :: IntMap a }
  deriving (Eq, Foldable, Functor, Ord, Semigroup, Show, Traversable)

instance Ixd.FunctorWithIndex (Key u) (KeyMap u) where
instance Ixd.FoldableWithIndex (Key u) (KeyMap u) where
instance Ixd.TraversableWithIndex (Key u) (KeyMap u) where
  itraverse f m = KeyMap <$> Ixd.itraverse (\i v -> f (Key i) v ) (getKeyMap m)

instance Eq1 (KeyMap u) where
  liftEq eq (KeyMap m1) (KeyMap m2) = liftEq eq m1 m2
  {-# INLINE liftEq #-}

emptyKeyMap :: KeyMap u a
emptyKeyMap = KeyMap IntMap.empty

insertKeyMap :: Key u -> a -> KeyMap u a -> KeyMap u a
insertKeyMap k v m = KeyMap (IntMap.insert (keyValue k) v (getKeyMap m))

lookupKeyMap :: Key u -> KeyMap u a -> Maybe a
lookupKeyMap k m = IntMap.lookup (keyValue k) (getKeyMap m)

---------------------------------------------------------------------
-- UnionFind

-- | Union-find data structure.
--
-- Unlike some implementations, this does not operate on a known, finite set of
-- values, but can be expanded post-creation. This is supported by a map from
-- values to keys, which requires @'Ord' a@.
--
-- This implementation supports annotations on root nodes. These annotations
-- should form a (commutative) 'Semigroup'. If annotations are not necessary,
-- you can use something like @()@ or 'Data.Proxy.Proxy'.
--
-- The 'Key' type provides infallable lookups, using the approach of
-- @justified-containers@. This requires not exporting the constructor of
-- 'UnionFind' (instead see 'empty') or that of 'Key'.
--
-- A note on terminology: This module uses \"root\" to mean \"equivalence class
-- representative\", because it\'s a lot shorter.
--
-- Type parameters:
--
-- - @u@: Type-level name for this union-find a la @justified-containers@
-- - @ann@: Annotation type (expected to be a 'Semigroup')
-- - @a@: Type of values
type UnionFind :: UnionFindName -> Type -> Type -> Type
data UnionFind u ann a
  = UnionFind
    -- Invariants:
    --
    -- 1. Every key in 'uf' is a value in 'keys'.
    -- 2. Every value in 'keys' is a key in 'uf'.
    -- 3. Every key in a 'Branch' in 'uf' is also a key of 'uf'.
    -- 4. Every @'Key' u@ that escapes this module is a key of @'keys' u@.
    { keys :: Map a (Key u)
      -- TODO: Benchmark using a 'Seq' here
    , uf :: KeyMap u (Branch u ann a)
    }
  deriving Show  -- for debugging only
-- This could probably be made faster by using a dynamic ST-array for 'uf' (a
-- la Rust @Vec@), and having keys be indices into that array. Perhaps 'Branch'
-- could be @UNPACK@ed (i.e., represented as an unboxed sum) into such an array
-- to avoid allocations and indirections. This would be good for cache locality,
-- avoid heap allocations, and make 'findByKey' @O(1)@. However, it wouldn't
-- improve the asymptotics of 'Equalities', which always starts by looking up a
-- value from 'keys'.

ufLiftEq2 ::
  (ann -> ann -> Bool) ->
  (a -> a -> Bool) ->
  UnionFind u ann a ->
  UnionFind u ann a ->
  Bool
ufLiftEq2 eqAnn eqVal u u' =
  liftEq2 eqVal (==) (keys u) (keys u') &&
    liftEq (liftEq2 eqAnn eqVal) (uf u) (uf u')

instance (Eq ann, Eq a) => Eq (UnionFind u ann a) where
  (==) = ufLiftEq2 (==) (==)

-- For union by size
data Sized ann
  = Sized
    { sizedSize :: {-# UNPACK #-} !(Sum Int)
    , sizedAnn :: ann
    }
  deriving (Functor, Show)

instance Eq a => Eq (Sized a) where
  (==) = liftEq (==)

instance Eq1 Sized where
  liftEq eqAnn (Sized sz1 ann1) (Sized sz2 ann2) = 
    sz1 == sz2 && eqAnn ann1 ann2

instance Semigroup ann => Semigroup (Sized ann) where
  Sized sz0 ann0 <> Sized sz1 ann1 = Sized (sz0 + sz1) (ann0 <> ann1)

size0 :: ann -> Sized ann
size0 = Sized (Sum 0)

size1 :: ann -> Sized ann
size1 = Sized (Sum 1)

-- | Not exported. See 'UnionFind' for type parameters.
type Branch :: UnionFindName -> Type -> Type -> Type
data Branch u ann a
  = Root (Annotated (Sized ann) a)
  | Branch {-# UNPACK #-} !(Key u)
  deriving (Functor, Show)

instance (Eq ann, Eq a) => Eq (Branch u ann a) where
  (==) = liftEq2 (==) (==)

instance Eq ann => Eq1 (Branch u ann) where
  liftEq = liftEq2 (==)

instance Eq2 (Branch u) where
  liftEq2 eqAnn eqVal b b' =
    case (b, b') of
      (Branch k, Branch k') -> k == k'
      (Root r, Root r') -> liftEq2 (liftEq eqAnn) eqVal r r'
      (Branch {}, Root {}) -> False
      (Root {}, Branch {}) -> False

instance Foldable (Branch u ann) where
  foldMap = foldMapDefault

instance Traversable (Branch u ann) where
  traverse f =
    \case
      Branch k -> pure (Branch k)
      Root r -> Root <$> traverse f r

data Annotated ann a
  = Annotated
    { annAnn :: ann
    , annVal :: a
    }
  deriving (Functor, Show)

instance (Eq ann, Eq a) => Eq (Annotated ann a) where
  (==) = liftEq2 (==) (==)

instance Eq ann => Eq1 (Annotated ann) where
  liftEq = liftEq2 (==)

instance Eq2 Annotated where
  liftEq2 eqAnn eqVal (Annotated ann1 val1) (Annotated ann2 val2) =
    eqAnn ann1 ann2 && eqVal val1 val2

instance Foldable (Annotated ann) where
  foldMap = foldMapDefault

instance Traversable (Annotated ann) where
  traverse f (Annotated ann val) = Annotated ann <$> f val

instance Bifunctor Annotated where
  bimap f g (Annotated ann val) = Annotated (f ann) (g val)

-- | Not exported
addAnn :: Semigroup ann => ann -> Annotated ann a -> Annotated ann a
addAnn ann val = val { annAnn = annAnn val <> ann }

-- | Not exported
unsize :: Annotated (Sized ann) a -> Annotated ann a
unsize (Annotated (Sized _ ann) a) = Annotated ann a

-- | Not exported
nextKey :: UnionFind u ann a -> Key u
nextKey u = Key (Map.size (keys u))

-- | A 'UnionFind' with a fresh type-level name @u@.
data SomeUnionFind ann a = forall u. SomeUnionFind (UnionFind u ann a)

empty :: SomeUnionFind ann a
empty = SomeUnionFind (UnionFind Map.empty emptyKeyMap)
-- TODO: with*

type Find :: UnionFindName -> Type -> Type -> Type
data Find u ann a
  = Find
    { -- | The 'Key' of the root node. Guaranteed to be present in @u@.
      findKey :: Key u
      -- | The possibly-modified union-find
    , findUnionFind :: UnionFind u ann a
      -- | The value of the root node and its annotation
    , findValue_ :: Annotated (Sized ann) a
    }
  deriving Show  -- for debugging only

findValue :: Find u ann a -> Annotated ann a
findValue = first sizedAnn . findValue_

findByKey ::
  Ord a =>
  UnionFind u ann a ->
  Key u ->
  Find u ann a
findByKey u k =
  case lookupKeyMap k (uf u) of
    -- Impossible due to invariants 2-4 on 'UnionFind'
    Nothing -> error ("findByKey: Bad key" ++ show (keyValue k))
    Just (Root r) -> Find k u r
    Just (Branch k') ->
      case lookupKeyMap k' (uf u) of
        -- Impossible due to invariant 2 on 'UnionFind'
        Nothing -> error ("findByKey: Bad key in `Branch`: " ++ show (keyValue k))
        Just parent ->
          -- Path compression
          let u' = u { uf = insertKeyMap k' parent (uf u) } in
          findByKey u' k'

findByValue :: Ord a => UnionFind u ann a -> a -> Maybe (Find u ann a)
findByValue u val = findByKey u <$> Map.lookup val (keys u)

-- | Are these two values equal in the union find?
equal ::
  Ord a =>
  UnionFind u ann a ->
  a ->
  a ->
  Bool
equal u x y =
  case (findByValue u y, findByValue u x) of
    (Just fx, Just fy) -> findKey fx == findKey fy
    _ -> False

-- | Return a set of equations that is sufficient to generate the rest via
-- reflexive-symmetric-transitive closure.
basis :: Ord a => UnionFind u ann a -> (UnionFind u ann a, [(Annotated ann a, a)])
basis u = foldr (uncurry go) (u, []) (Map.toList (keys u))
  where
    go val key (u', eqs) =
      let f = findByKey u' key in
      let root = unsize (findValue_ f) in
      (findUnionFind f, (root, val) : eqs)

-- Helper, not exported
insertRoot ::
  UnionFind u ann a ->
  Key u ->
  Annotated (Sized ann) a ->
  UnionFind u ann a
insertRoot u k root = u { uf = insertKeyMap k (Root root) (uf u) }
  
-- Helper, not exported
insertBranch ::
  UnionFind u ann a ->
  -- | 'Branch' key
  Key u ->
  -- | 'Root' key
  Key u ->
  UnionFind u ann a
insertBranch u kb kr = u { uf = insertKeyMap kb (Branch kr) (uf u) }

-- | Insert a value, combining annotations if it is present
insert ::
  Ord a =>
  Semigroup ann =>
  UnionFind u ann a ->
  a ->
  ann ->
  Find u ann a
insert u val ann =
  case findByValue u val of
    Just f@(Find { findKey = k, findValue_ = v, findUnionFind = u' }) ->
      f { findUnionFind = insertRoot u' k (addAnn (size0 ann) v) }
    Nothing ->
      let k = nextKey u in
      let u' = u { keys = Map.insert val k (keys u) } in
      let root = Annotated (size1 ann) val in
      Find
      { findKey = k
      , findValue_ = root
      , findUnionFind = insertRoot u' k root
      }

-- Not exported
unionByRoots ::
  Ord a =>
  Semigroup ann =>
  UnionFind u ann a ->
  (Key u, Annotated (Sized ann) a) ->
  (Key u, Annotated (Sized ann) a) ->
  (UnionFind u ann a, Find u ann a)
unionByRoots u (k1, r1) (k2, r2) =
  if k1 == k2
  then (u, Find k1 u r1)
  else
    let a1 = annAnn r1 in
    let a2 = annAnn r2 in
    -- Union by size: The smaller points to the bigger, the bigger points to
    -- itself with a modified annotation.
    if sizedSize a1 < sizedSize a2
    then
      let u' = insertBranch (insertRoot u k2 (addAnn a1 r2)) k1 k2 in
      (u', Find k2 u' r2)
    else
      let u' = insertBranch (insertRoot u k1 (addAnn a2 r1)) k2 k1 in
      (u', Find k1 u' r1)

-- | Make two existing values equal by key
unionByKey ::
  Ord a =>
  Semigroup ann =>
  UnionFind u ann a ->
  Key u ->
  Key u ->
  (UnionFind u ann a, Find u ann a)
unionByKey u k1 k2 =
  case findByKey u k1 of
    Find { findKey = k1', findUnionFind = u', findValue_ = r1 } ->
      case findByKey u' k2 of
        f2@(Find { findKey = k2', findUnionFind = u'', findValue_ = r2 }) ->
          if k1 == k2
          then (u'', f2)
          else unionByRoots u'' (k1', r1) (k2', r2)

-- | Make two values equal, inserting them if not present
unionByValue ::
  Ord a =>
  Semigroup ann =>
  UnionFind u ann a ->
  Annotated ann a ->
  Annotated ann a ->
  (UnionFind u ann a, Find u ann a)
unionByValue u annd1 annd2 =
  case insert u (annVal annd1) (annAnn annd1) of
    Find { findKey = k1, findValue_ = r1, findUnionFind = u' } ->
      case insert u' (annVal annd2) (annAnn annd2) of
        f2@(Find { findKey = k2, findValue_ = r2, findUnionFind = u'' }) ->
          if k1 == k2
          then (u'', f2)
          else unionByRoots u'' (k1, r1) (k2, r2)

mapBranchAnn ::
  Ord a =>
  (ann -> ann') ->
  Branch u ann a ->
  Branch u ann' a
mapBranchAnn f =
  \case
    Branch k' -> Branch k'
    Root r -> Root (Annotated (f <$> annAnn r) (annVal r))

mapAnn :: Ord a => (ann -> ann') -> UnionFind u ann a -> UnionFind u ann' a
mapAnn f u = u { uf = fmap (mapBranchAnn f) (uf u) }

traverseUnionFind ::
  Applicative f =>
  Ord b =>
  (a -> f b) ->
  UnionFind u ann a ->
  f (UnionFind u ann b)
traverseUnionFind f u =
  UnionFind 
    <$> fmap Map.fromList (traverse (\(k, v) -> (,v) <$> f k) (Map.toList (keys u)))
    <*> traverse (traverse f) (uf u)
