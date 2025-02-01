{-|
Module      : What4.Expr.BoolMap
Description : Datastructure for representing a conjunction of predicates
Copyright   : (c) Galois Inc, 2019-2020
License     : BSD3
Maintainer  : rdockins@galois.com

Declares a datatype for representing n-way conjunctions or disjunctions
in a way that efficiently captures important algebraic
laws like commutativity, associativity and resolution.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module What4.Expr.BoolMap
  ( BoolMap
  , var
  , addVar
  , fromVars
  , combine
  , Polarity(..)
  , negatePolarity
  , contains
  , isInconsistent
  , isNull
  , BoolMapView(..)
  , viewBoolMap
  , traverseVars
  , reversePolarities
  , removeVar
  , Wrap(..)
    -- * 'ConjMap'
  , ConjMap(..)
  , ConjMapView
  , pattern ConjTrue
  , pattern ConjFalse
  , pattern Conjuncts
  , viewConjMap
  , addConjunct
  , evalConj
  ) where

import           Control.Lens (_1, over)
import           Data.Hashable
import qualified Data.List as List (foldl')
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Kind (Type)
import           Data.Parameterized.Classes

import           What4.BaseTypes
import qualified What4.Utils.AnnotatedMap as AM
import           What4.Utils.IncrHash
import Data.Coerce (coerce)

-- | Describes the occurrence of a variable or expression, whether it is
--   negated or not.
data Polarity = Positive | Negative
 deriving (Eq,Ord,Show)

instance Hashable Polarity where
  hashWithSalt s Positive = hashWithSalt s (0::Int)
  hashWithSalt s Negative = hashWithSalt s (1::Int)

-- | Swap a polarity value
negatePolarity :: Polarity -> Polarity
negatePolarity Positive = Negative
negatePolarity Negative = Positive

newtype Wrap (f :: k -> Type) (x :: k) = Wrap { unWrap:: f x }

instance TestEquality f => Eq (Wrap f x) where
  Wrap a == Wrap b = isJust $ testEquality a b
instance OrdF f => Ord (Wrap f x) where
  compare (Wrap a) (Wrap b) = toOrdering $ compareF a b
instance (HashableF f, TestEquality f) => Hashable (Wrap f x) where
  hashWithSalt s (Wrap a) = hashWithSaltF s a

-- | This data structure keeps track of a collection of expressions
--   together with their polarities. Such a collection might represent
--   either a conjunction or a disjunction of expressions.  The
--   implementation uses a map from expression values to their
--   polarities, and thus automatically implements the associative,
--   commutative and idempotency laws common to both conjunctions and
--   disjunctions.  Moreover, if the same expression occurs in the
--   collection with opposite polarities, the entire collection
--   collapses via a resolution step to an \"inconsistent\" map.  For
--   conjunctions this corresponds to a contradiction and
--   represents false; for disjunction, this corresponds to the law of
--   the excluded middle and represents true.
--
--   The annotation on the 'AM.AnnotatedMap' is an incremental hash ('IncrHash')
--   of the map, used to support a fast 'Hashable' instance.

data BoolMap (f :: BaseType -> Type)
  = InconsistentMap
  | BoolMap !(AM.AnnotatedMap (Wrap f BaseBoolType) IncrHash Polarity)

instance OrdF f => Eq (BoolMap f) where
  InconsistentMap == InconsistentMap = True
  BoolMap m1 == BoolMap m2 = AM.eqBy (==) m1 m2
  _ == _ = False

instance OrdF f => Semigroup (BoolMap f) where
  (<>) = combine

-- | Traverse the expressions in a bool map, and rebuild the map.
traverseVars :: (Applicative m, HashableF g, OrdF g) =>
  (f BaseBoolType -> m (g (BaseBoolType))) ->
  BoolMap f -> m (BoolMap g)
traverseVars _ InconsistentMap = pure InconsistentMap
traverseVars f (BoolMap m) =
  fromVars <$> traverse (_1 (f . unWrap)) (AM.toList m)

elementHash :: HashableF f => f BaseBoolType -> Polarity -> IncrHash
elementHash x p = mkIncrHash (hashWithSaltF (hash p) x)

instance (OrdF f, HashableF f) => Hashable (BoolMap f) where
  hashWithSalt s InconsistentMap = hashWithSalt s (0::Int)
  hashWithSalt s (BoolMap m) =
    case AM.annotation m of
      Nothing -> hashWithSalt s (1::Int)
      Just h  -> hashWithSalt (hashWithSalt s (1::Int)) h

-- | Represents the state of a bool map
data BoolMapView f
  = BoolMapUnit
       -- ^ A bool map with no expressions, represents the unit of the corresponding operation
  | BoolMapDualUnit
       -- ^ An inconsistent bool map, represents the dual of the operation unit
  | BoolMapTerms (NonEmpty (f BaseBoolType, Polarity))
       -- ^ The terms appearing in the bool map, of which there is at least one

-- | Deconstruct the given bool map for later processing
viewBoolMap :: BoolMap f -> BoolMapView f
viewBoolMap InconsistentMap = BoolMapDualUnit
viewBoolMap (BoolMap m) =
  case AM.toList m of
    []  -> BoolMapUnit
    (Wrap x,p):xs -> BoolMapTerms ((x,p):|(map (over _1 unWrap) xs))

-- | Returns true for an inconsistent bool map
isInconsistent :: BoolMap f -> Bool
isInconsistent InconsistentMap = True
isInconsistent _ = False

-- | Returns true for a \"null\" bool map with no terms
isNull :: BoolMap f -> Bool
isNull InconsistentMap = False
isNull (BoolMap m) = AM.null m

-- | Produce a singleton bool map, consisting of just the given term
var :: (HashableF f, OrdF f) => f BaseBoolType -> Polarity -> BoolMap f
var x p = BoolMap (AM.singleton (Wrap x) (elementHash x p) p)

-- | Add a variable to a bool map, performing a resolution step if possible
addVar :: (HashableF f, OrdF f) => f BaseBoolType -> Polarity -> BoolMap f -> BoolMap f
addVar _ _ InconsistentMap = InconsistentMap
addVar x p1 (BoolMap bm) = maybe InconsistentMap BoolMap $ AM.alterF f (Wrap x) bm
 where
 f Nothing = return (Just (elementHash x p1, p1))
 f el@(Just (_,p2)) | p1 == p2  = return el
                    | otherwise = Nothing

-- | Generate a bool map from a list of terms and polarities by repeatedly
--   calling @addVar@.
fromVars :: (HashableF f, OrdF f) => [(f BaseBoolType, Polarity)] -> BoolMap f
fromVars = List.foldl' (\m (x,p) -> addVar x p m) (BoolMap AM.empty)

-- | Merge two bool maps, performing resolution as necessary.
combine :: OrdF f => BoolMap f -> BoolMap f -> BoolMap f
combine InconsistentMap _ = InconsistentMap
combine _ InconsistentMap = InconsistentMap
combine (BoolMap m1) (BoolMap m2) =
    maybe InconsistentMap BoolMap $ AM.mergeA f m1 m2

  where f _k (v,p1) (_,p2)
          | p1 == p2  = Just (v,p1)
          | otherwise = Nothing

-- | Test if the bool map contains the given term, and return the polarity
--   of that term if so.
contains :: OrdF f => BoolMap f -> f BaseBoolType -> Maybe Polarity
contains InconsistentMap _ = Nothing
contains (BoolMap m) x = snd <$> AM.lookup (Wrap x) m

-- | Swap the polarities of the terms in the given bool map.
reversePolarities :: OrdF f => BoolMap f -> BoolMap f
reversePolarities InconsistentMap = InconsistentMap
reversePolarities (BoolMap m) = BoolMap $! fmap negatePolarity m

-- | Remove the given term from the bool map.  The map is unchanged
--   if inconsistent or if the term does not occur.
removeVar :: OrdF f => BoolMap f -> f BaseBoolType -> BoolMap f
removeVar InconsistentMap _ = InconsistentMap
removeVar (BoolMap m) x = BoolMap (AM.delete (Wrap x) m)

--------------------------------------------------------------------------------
-- ConjMap

-- No idea why `coerce` needs these the explicit type applications in this
-- section...

-- | A 'BoolMap' representing a conjunction.
newtype ConjMap f = ConjMap { getConjMap :: BoolMap f }
  deriving (Eq, Hashable, Semigroup)

-- | Represents the state of a 'ConjMap'. See 'viewConjMap'.
--
-- Like 'BoolMapView', but with more specific patterns for readability.
newtype ConjMapView f = ConjMapView (BoolMapView f)

pattern ConjTrue :: ConjMapView f
pattern ConjTrue = ConjMapView BoolMapUnit

pattern ConjFalse :: ConjMapView f
pattern ConjFalse = ConjMapView BoolMapDualUnit

pattern Conjuncts :: NonEmpty (f BaseBoolType, Polarity) -> ConjMapView f
pattern Conjuncts ts = ConjMapView (BoolMapTerms ts)

{-# COMPLETE ConjTrue, ConjFalse, Conjuncts #-}

-- | Deconstruct the given 'ConjMap' for later processing
viewConjMap :: forall f. ConjMap f -> ConjMapView f
viewConjMap =
  coerce @(BoolMap f -> BoolMapView f) @(ConjMap f -> ConjMapView f) viewBoolMap
{-# INLINE viewConjMap #-}

addConjunct ::
  forall f.
  (HashableF f, OrdF f) =>
  f BaseBoolType ->
  Polarity ->
  ConjMap f ->
  ConjMap f
addConjunct =
  coerce
    @(f BaseBoolType -> Polarity -> BoolMap f -> BoolMap f)
    @(f BaseBoolType -> Polarity -> ConjMap f -> ConjMap f)
    addVar
{-# INLINE addConjunct #-}

evalConj :: Applicative m => (f BaseBoolType -> m Bool) -> ConjMap f -> m Bool
evalConj f cm =
  let pol (x, Positive) = f x
      pol (x, Negative) = not <$> f x
  in
  case viewConjMap cm of
    ConjTrue -> pure True
    ConjFalse -> pure False
    Conjuncts (t:|ts) ->
      List.foldl' (&&) <$> pol t <*> traverse pol ts
