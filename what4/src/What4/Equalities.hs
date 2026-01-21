{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | See "What4.ExprEqualities".
module What4.Equalities
  ( Equalities
  , Find(..)
    -- ** Construction
  , empty
  , fromEqual
  , fromNotEqual
    -- ** Queries
  , checkEqual
  , checkNotEqual
  , Equation(..)
  , Inequation(..)
  , ppEquation
  , ppInequation
  , Basis(..)
  , basis
  , toBasis
  , hasTrivialEqs
  , hasInconsistentIneqs
  , ppBasisEqs
    -- ** Modifications
  , equal
  , notEqual
  , and
  , traverseEqualities
  , not
  ) where

import Control.Monad (foldM)
import Data.Kind (Type)
import Data.Maybe qualified as Maybe
import Data.Parameterized.Classes
import Data.Parameterized.Some (Some(Some))
import Prelude hiding (and, not)
import Prettyprinter qualified as PP
import What4.UnionFindF qualified as UF
import What4.UnionFind qualified as BaseUF
import Unsafe.Coerce (unsafeCoerce)

data Equalities f
  = forall u.
    Equalities
    -- Invariant: The keys in the 'UF.KeySet' on the roots all point to values
    -- of the same type as the root. This is upheld by 'notEqual', which
    -- requires values of the same type @f x@.
    { _getEqualities :: UF.UnionFind u (UF.KeySet u) f }

instance TestEquality f => Eq (Equalities f) where
  Equalities u == Equalities u' =
    UF.ufLiftEq2 UF.eqKeySets (\x y -> isJust (testEquality x y)) u u'

instance (HashableF f, TestEquality f) => Hashable (Equalities f) where
  hashWithSalt = error "TODO"

instance (EqF f, OrdF f, ShowF f) => PP.Pretty (Equalities f) where
  pretty =
    PP.concatWith (\x y -> PP.hsep [x, PP.pretty "∧", y]) . ppBasisEqs . toBasis

empty :: (EqF f, OrdF f) => Equalities f
empty =
  case UF.empty of
    UF.SomeUnionFind uf ->
      Equalities (UF.mapAnn (const UF.emptyKeySet) uf)

-- | @'fromEqual' x y == 'fst' ('equal' 'empty' x y)@
fromEqual ::
  EqF f =>
  OrdF f =>
  f x ->
  f x ->
  Equalities f
fromEqual x y = findEqualities (Maybe.fromJust (equal empty x y))
-- TODO: comment on fromJust

-- | @'fromNotEqual' x y == 'notEqual' 'empty' x y@
fromNotEqual ::
  EqF f =>
  OrdF f =>
  f x ->
  f x ->
  Maybe (Equalities f)
fromNotEqual = notEqual empty

-- | Are these two values equal in the union find?
checkEqual ::
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  Maybe (Find f x)
checkEqual (Equalities e) x y = fromFind <$> UF.equal e x y
{-# INLINE checkEqual #-}

-- | Are these two values not equal in the union find?
checkNotEqual ::
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  Bool  -- TODO: return the updated union-find
checkNotEqual (Equalities u) x y =
  let fx = UF.insert u x UF.emptyKeySet in
  let fy = UF.insert (UF.findUnionFind fx) y UF.emptyKeySet in
  let kx = UF.findKey fx in
  let ky = UF.findKey fy in
  let notEqXKeys = BaseUF.annAnn (UF.findValue fx) in
  let notEqYKeys = BaseUF.annAnn (UF.findValue fy) in
  UF.memberKeySet kx notEqYKeys || UF.memberKeySet ky notEqXKeys

data Equation f = forall x. Equation { eqLhs :: f x, eqRhs :: f x }
data Inequation f = forall x. Inequation { neqLhs :: f x, neqRhs :: f x }

ppEquation :: (forall x. f x -> PP.Doc ann) -> Equation f -> PP.Doc ann
ppEquation pp (Equation lhs rhs) =
  PP.hsep [pp lhs, PP.pretty "=", pp rhs]

ppInequation :: (forall x. f x -> PP.Doc ann) -> Inequation f -> PP.Doc ann
ppInequation pp (Inequation lhs rhs) =
  PP.hsep [pp lhs, PP.pretty "!=", pp rhs]

instance ShowF f => PP.Pretty (Equation f) where
  pretty = ppEquation (PP.pretty. showF)

instance ShowF f => PP.Pretty (Inequation f) where
  pretty = ppInequation (PP.pretty. showF)

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
          -- TODO: probably merge with ineqs from b?
        , basisInequations = ineqs
        }
      )

toBasis :: (EqF f, OrdF f) => Equalities f -> Basis f
toBasis = snd . basis
{-# INLINE toBasis #-}

-- TODO: Equations aren't trivial if they have inequalities
hasTrivialEqs :: (EqF f, OrdF f) => Equalities f -> Bool
hasTrivialEqs (Equalities u) = UF.hasTrivialEqs u
{-# INLINE hasTrivialEqs #-}

hasInconsistentIneqs :: (EqF f, OrdF f) => Equalities f -> Bool
hasInconsistentIneqs = any inconsistent . basisInequations . toBasis
  where inconsistent (Inequation lhs rhs) = eqF lhs rhs

ppBasisEqs :: (EqF f, OrdF f, ShowF f) => Basis f -> [PP.Doc ann]
ppBasisEqs b =
  map PP.pretty (basisEquations b) ++ map PP.pretty (basisInequations b)

-- TODO? Add inequality keys? Would require type-level name for Equalities.
type Find :: (k -> Type) -> k -> Type
data Find f x
  = Find
    { findEqualities :: Equalities f
      -- | The value of the root node
    , findValue :: f x
    }

fromFind ::
  UF.Find u (UF.KeySet u) f x ->
  Find f x
fromFind f =
  Find
  { findEqualities = Equalities (UF.findUnionFind f)
  , findValue = BaseUF.annVal (UF.findValue f)
  }

equal ::  -- TODO: reuse checkNotEqual
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  Maybe (Find f x)
equal (Equalities u) x y =
  let fx = UF.insert u x UF.emptyKeySet in
  let fy = UF.insert (UF.findUnionFind fx) y UF.emptyKeySet in
  let u' = UF.findUnionFind fy in
  let kx = UF.findKey fx in
  let ky = UF.findKey fy in
  let notEqXKeys = BaseUF.annAnn (UF.findValue fx) in
  let notEqYKeys = BaseUF.annAnn (UF.findValue fy) in
  if | kx == ky -> Just (fromFind fy)
     | UF.memberKeySet kx notEqYKeys -> Nothing
     | UF.memberKeySet ky notEqXKeys -> Nothing
     | otherwise ->
        let (_, f) = UF.unionByKey u' kx ky in
        Just (fromFind f)

notEqual ::
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  Maybe (Equalities f)
  -- TODO: Store the inequality in both roots
notEqual (Equalities u) x y =
  -- Store the inequality in the root of the lesser
  --
  -- TODO: Should probably store it in the *lesser root*
  case compareF x y of
    EQF -> Nothing
    GTF ->
      let fx = UF.insert u x UF.emptyKeySet in
      let fy = UF.insert (UF.findUnionFind fx) y (UF.singletonKeySet (UF.findKey fx)) in
      if UF.findKey fx == UF.findKey fy
      then Nothing
      else Just (Equalities (UF.findUnionFind fy))
    LTF ->
      let fy = UF.insert u y UF.emptyKeySet in
      let fx = UF.insert (UF.findUnionFind fy) x (UF.singletonKeySet (UF.findKey fy)) in
      if UF.findKey fx == UF.findKey fy
      then Nothing
      else Just (Equalities (UF.findUnionFind fx))

and ::
  (EqF f, OrdF f) =>
  Equalities f ->
  Equalities f ->
  Maybe (Equalities f)
and x y = do
  let b = toBasis y
  x' <- foldM (\es (Equation lhs rhs) -> fmap findEqualities (equal es lhs rhs)) x (basisEquations b)
  foldM (\es (Inequation lhs rhs) -> notEqual es lhs rhs) x' (basisInequations b)

traverseEqualities ::
  Applicative m =>
  EqF g =>
  OrdF g =>
  (forall x. f x -> m (g x)) ->
  Equalities f ->
  m (Equalities g)
traverseEqualities f (Equalities u) = Equalities <$> UF.traverseUnionFind f u

-- | Attempt to negate a singleton 'Equalities'
not ::
  (EqF f, OrdF f) =>
  Equalities f ->
  Maybe (Equalities f)
not u =
  case toBasis u of
    -- not (x = y) iff x != y
    Basis [Equation lhs rhs] [] -> fromNotEqual lhs rhs
    -- not (x != y) iff x = y
    -- TODO: this won't fire bc bases have too many elements
    Basis [] [Inequation lhs rhs] -> Just (fromEqual lhs rhs)
    _ -> Nothing

