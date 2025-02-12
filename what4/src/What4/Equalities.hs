{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module What4.Equalities
  ( Equalities
  , empty
  , fromEqual
  , equal
  , notEqual
  , traverseEqualities
  , Equation(..)
  , Inequation(..)
  , Basis(..)
  , basis
  , toBasis
  ) where

import Data.Parameterized.Classes
import Data.Parameterized.Some (Some(Some))
import qualified What4.UnionFindF as UF
import Unsafe.Coerce (unsafeCoerce)

data Equalities f
  = forall u.
    Equalities
    -- Invariant: The keys in the 'UF.KeySet' on the roots all point to values
    -- of the same type as the root. This is upheld by 'notEqual', which
    -- requires values of the same type @f x@.
    { _getEqualities :: UF.UnionFind u (UF.KeySet u) f }

instance TestEquality f => Eq (Equalities f) where
  -- Let's just ignore that pesky type variable...
  --
  -- TODO: Make a unsafe helper function upstream
  Equalities u == Equalities u' = u == (unsafeCoerce u')

instance (HashableF f, TestEquality f) => Hashable (Equalities f) where
  hashWithSalt = error "TODO"

empty :: (EqF f, OrdF f) => Equalities f
empty =
  case UF.empty of
    UF.SomeUnionFind uf ->
      Equalities (UF.mapAnn (const UF.emptyKeySet) uf)

-- | @'fromEqual' == 'equal' 'empty'@
fromEqual ::
  EqF f =>
  OrdF f =>
  f x ->
  f x ->
  Equalities f
fromEqual = equal empty

equal ::
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  Equalities f
equal (Equalities u) x y =
  let fx = UF.insert u x UF.emptyKeySet in
  let fy = UF.insert (UF.findUnionFind fx) y UF.emptyKeySet in
  Equalities
    (UF.unionByKey (UF.findUnionFind fy) (UF.findKey fx) (UF.findKey fy))

notEqual ::
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  Equalities f
notEqual (Equalities u) x y =
  -- Store the inequality in the root of the lesser
  --
  -- TODO: Should probably store it in the *lesser root*
  case compareF x y of
    GTF -> 
      let fx = UF.insert u x UF.emptyKeySet in
      let fy = UF.insert (UF.findUnionFind fx) y (UF.singletonKeySet (UF.findKey fx)) in
      Equalities (UF.findUnionFind fy)
    LTF -> 
      let fy = UF.insert u y UF.emptyKeySet in
      let fx = UF.insert (UF.findUnionFind fy) x (UF.singletonKeySet (UF.findKey fy)) in
      Equalities (UF.findUnionFind fx)
    EQF -> error "don't do that"

traverseEqualities ::
  Applicative m =>
  EqF g =>
  OrdF g =>
  (forall x. f x -> m (g x)) ->
  Equalities f ->
  m (Equalities g)
traverseEqualities f (Equalities u) = Equalities <$> UF.traverseUnionFind f u

data Equation f = forall x. Equation { eqLhs :: f x, eqRhs :: f x }
data Inequation f = forall x. Inequation { neqLhs :: f x, neqRhs :: f x }

data Basis f 
  = Basis
  { basisEquations :: [Equation f]
  , basisInequations :: [Inequation f]
  }

-- | Not exported
emptyBasis :: Basis f
emptyBasis = Basis [] []

-- Helper, not exported
inequations ::
  EqF f =>
  OrdF f =>
  UF.UnionFind u (UF.KeySet u) f ->
  f x ->
  UF.KeySet u ->
  (UF.UnionFind u (UF.KeySet u) f, [Inequation f])
inequations u root ineqKeys = foldr mkIneq (u, []) (UF.keySetToList ineqKeys)
  where
    mkIneq (Some k) (u', ineqs) =
      let f = UF.findByKey u' k in
      -- See invariant on 'Equalities'
      let root' = unsafeCoerce root in
      let ineq = Inequation (UF.annVal (UF.findValue f)) root' in
      (UF.findUnionFind f, ineq : ineqs)

-- | Enough (in)equalities to generate all of the rest
basis :: (EqF f, OrdF f) => Equalities f -> (Equalities f, Basis f)
basis (Equalities u) = 
  let (u', eqs) = UF.basis u in
  let (u'', b) = foldr go (u', emptyBasis) eqs in
  (Equalities u'', b)
  where
    go (UF.Equation (UF.Annotated ineqKeys lhs) rhs) (u', b) =
      let (u'', ineqs) = inequations u' lhs ineqKeys in
      ( u''
      , b
        { basisEquations = Equation lhs rhs : basisEquations b
        , basisInequations = ineqs
        }
      )

toBasis :: (EqF f, OrdF f) => Equalities f -> Basis f
toBasis = snd . basis
{-# INLINE toBasis #-}
