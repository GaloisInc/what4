-- TODO: When adding `p == True`, look for `~ p == True`, etc.
-- TODO: Helpers for conjunction
-- TODO: When to consider abstract domains?

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | 'ExprEqualities' efficiently stores conjunctions of (dis)equalities.
--
-- -- * Background
--
-- What4 tries hard to keep symbolic expressions as simple as possible.
-- It does so using at least three techniques:
--
-- * Local rewrites when expressions are constructed (see "What4.Expr.Builder").
--   Such rewrites often result in a partially normalized format for expressions
--   of a given type.
-- * Abstract domains (see "What4.Utils.AbstractDomains").
-- * Data structures that by their very structure (partially) normalize
--   expressions of the given kind (see "What4.Expr.WeightedSum").
--
-- 'ExprEqualities' is this last kind of data structure.
--
-- -- * Spec
--
-- The semi-normal form that 'ExprEqualities' provides can be understood at
-- a high level as applying the following rewrite rules:
--
-- * Reflexivity: @x = x@
-- * Symmetry: @x = y --> y = x@
-- * Transitivity: @x = y and y = z --> x = z@
-- * Commutativity of @and@: @x = y and u = v --> u = v and x = y@
-- * Associativity of @and@
-- * Idempotence of @and@: @x = y and x = y --> x = y@
-- * Collapse: @x = y and x /= y --> false@
--
-- All but the last rule can be thought of as being applied /eagerly/ and
-- /losslessly/, i.e., as if they were applied to fixpoint after every operation
-- on 'ExprEqualities'. The last rule is applied more /lazily/: only upon
-- insertion of either @x = y@ or @x /= y@, and then on certain operations that
-- consume 'ExprEqualities' (e.g., 'toBasis').
--
-- 'ExprEqualities' is further used to store /arbitrary/ conjunctions via the
-- identities
--
-- * @x --> x = true@
-- * @not x --> x = false@
--
-- We can derive the effective rewrite rules for such conjunctions from those
-- for equalities.
--
-- * Commutativity of @and@ for general predicates
-- * Associativity of @and@ for general predicates
-- * Idempotence of @and@ for general predicates
-- * Collapse of @and@: @x and (not x) --> false@
--
-- TODO: Property-based tests for these!
--
-- -- * Implementation details
--
-- At the lowest level, 'ExprEqualities' is built on a union-find data
-- structure. This structure is refined and extended throughout several layers
-- of abstraction, each with their own safety and correctness invariants:
--
-- * "What4.UnionFind" provides @'What4.UnionFind.UnionFind' u ann a@, a
--   union-find data structure with /annotations/ in the commutative semigroup
--   @ann@ which are collected at root nodes (i.e., equivalence class
--   representatives).
-- * "What4.UnionFindF" provides a wrapper around this basic union find for
--   working with /parameterized/ types like 'What4.Expr.Builder.Expr'.
-- * "What4.Equalities" specializes the annotation type to be a set of keys in
--   the union-find (with set union as the semigroup operation), denoting the
--   set of values that the equivalence class is known to /not/ be equal to
--   (i.e., disequalities).
--
-- Finally, 'ExprEqualities' is a wrapper around 'What4.Equalities' for working
-- specifically with instances of 'WI.IsExpr'.
module What4.ExprEqualities
  ( ExprEqualities
  , Result(..)
    -- ** Construction
  , empty
  , fromEqual
    -- ** Queries
  , checkEqual
  , checkNotEqual
  , toBasis
    -- ** Modifications
  , equal
  , notEqual
  , traverseExprEqualities
  , union
  ) where

import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Parameterized.Classes
import Prelude
import qualified What4.Interface as WI
import qualified What4.Equalities as Eqs
import qualified What4.Utils.AbstractDomains as WA

-- Note [Inline]: Several functions in this module are parametric on `f`, which
-- is generally instantiated to `Expr` and `x`, which is often instantiated to
-- a specific `BaseType`. We really want these functions to be inlined until
-- they can actually be specialized for those types to avoid `case`-splits on
-- the `BaseType`.

-- |  'ExprEqualities' efficiently stores conjunctions of (dis)equalities.
--
-- It has a few "invariants" that are not locally enforced by this module, but
-- rather require cooperation from API clients. These are not safety invariants,
-- but just semi-normal forms that help with rewriting.
--
-- * It should not contain @not x = true@ nor @not x = false@. TODO helpers
-- * It should not contain "trivial" (dis)equalities as determined by
--   'definitelyEqual' and 'definitelyNotEqual'.
type ExprEqualities :: (WI.BaseType -> Type) -> Type
newtype ExprEqualities f
  = ExprEqualities { _getEqualities :: Eqs.Equalities f }
  deriving (Eq, Hashable)

type Result :: (WI.BaseType -> Type) -> Type
data Result f
  = ResTrue
  | ResFalse
  | Equalities (ExprEqualities f)

empty :: (EqF f, OrdF f) => ExprEqualities f
empty = ExprEqualities Eqs.empty

-- | @'fromEqual' == 'equal' 'empty'@
fromEqual ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  f x ->
  f x ->
  Result f
fromEqual x y
  | definitelyEqual x y = ResTrue
  | definitelyNotEqual x y = ResFalse
  | otherwise = equal empty x y
{-# INLINE fromEqual #-}

-- | @'fromNotEqual' == 'notEqual' 'empty'@
fromNotEqual ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  f x ->
  f x ->
  Result f
fromNotEqual x y
  | definitelyEqual x y = ResFalse
  | definitelyNotEqual x y = ResTrue
  | otherwise = notEqual empty x y
{-# INLINE fromNotEqual #-}

-- | Are these two values equal in the union find?
checkEqual ::
  EqF f =>
  OrdF f =>
  ExprEqualities f ->
  f x ->
  f x ->
  Bool  -- TODO: return the updated union-find
checkEqual (ExprEqualities e) = Eqs.checkEqual e
{-# INLINE checkEqual #-}

-- | Are these two values inequal in the union find?
checkNotEqual ::
  EqF f =>
  OrdF f =>
  ExprEqualities f ->
  f x ->
  f x ->
  Bool
checkNotEqual (ExprEqualities e) = Eqs.checkNotEqual e

toBasis :: (EqF f, OrdF f) => ExprEqualities f -> Eqs.Basis f
toBasis = coerce Eqs.toBasis
{-# INLINE toBasis #-}

definitelyEqual ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  f x ->
  f x ->
  Bool
definitelyEqual x y
 | eqF x y = True
 | Just x' <- WI.asConcrete x
 , Just y' <- WI.asConcrete y = x' == y'
 | otherwise = False
{-# INLINE definitelyEqual #-}  -- See Note [Inline]

definitelyNotEqual ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  f x ->
  f x ->
  Bool
definitelyNotEqual x y
 | eqF x y = False
 | Just x' <- WI.asConcrete x
 , Just y' <- WI.asConcrete y = x' /= y'
 | let t = WI.exprType x
 , let ax = WA.getAbsValue x
 , let ay = WA.getAbsValue y
 , WA.withAbstractable t (not (WA.avOverlap t ax ay)) = True
 | otherwise = False
{-# INLINE definitelyNotEqual #-}  -- See Note [Inline]

equal ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  ExprEqualities f ->
  f x ->
  f x ->
  Result f
equal (ExprEqualities e) x y
 | definitelyNotEqual x y = ResFalse  -- TODO: Make this an assert
 | Just f <- Eqs.equal e x y =
   let root = Eqs.findValue f in
   if definitelyNotEqual x root || definitelyNotEqual y root
   then ResFalse
   else Equalities (ExprEqualities (Eqs.findEqualities f))
 | otherwise = ResFalse
{-# INLINABLE equal #-}  -- See Note [Inline]
 -- TODO: Check for incompatibilities with inequalities?

notEqual ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  ExprEqualities f ->
  f x ->
  f x ->
  Result f
notEqual (ExprEqualities e) x y
  | definitelyEqual x y = ResFalse  -- TODO: Make this an assert
  | otherwise =
      case Eqs.notEqual e x y of
        Nothing -> ResFalse
        Just e' -> Equalities (ExprEqualities e')
 -- TODO: Check for incompatibilities with inequalities?
{-# INLINABLE notEqual #-}  -- See Note [Inline]

traverseExprEqualities ::
  Applicative m =>
  EqF g =>
  OrdF g =>
  (forall x. f x -> m (g x)) ->
  ExprEqualities f ->
  m (ExprEqualities g)
traverseExprEqualities f (ExprEqualities e) =
  ExprEqualities <$> Eqs.traverseEqualities f e

union ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  ExprEqualities f ->
  ExprEqualities f ->
  Result f
union l r =
  let br = toBasis r
      addEq (Eqs.Equation lhs rhs) mbE =
        case mbE of
          ResFalse -> ResFalse
          ResTrue -> fromEqual lhs rhs
          Equalities e -> equal e lhs rhs
      addIneq (Eqs.Inequation lhs rhs) mbE =
        case mbE of
          ResFalse -> ResFalse
          ResTrue -> fromNotEqual lhs rhs
          Equalities e -> notEqual e lhs rhs
  in
    case foldr addEq (Equalities l) (Eqs.basisEquations br) of
      ResFalse -> ResFalse
      ResTrue -> foldr addIneq (Equalities l) (Eqs.basisInequations br)
      l' -> foldr addIneq l' (Eqs.basisInequations br)
