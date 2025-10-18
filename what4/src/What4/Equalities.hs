{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module What4.Equalities
  ( Equalities
  , empty
  , Find(..)
  , fromEqual
  , equal
  , notEqual
  , traverseEqualities
  , Equation(..)
  , Inequation(..)
  , ppEquation
  , ppInequation
  , Basis(..)
  , basis
  , toBasis
  , ppBasisEqs
  , and
  ) where

import Control.Monad (foldM)
import Data.Kind (Type)
import Data.Parameterized.Classes
import Data.Parameterized.Some (Some(Some))
import Prelude hiding (and)
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
  -- Let's just ignore that pesky type variable...
  --
  -- TODO: Make a unsafe helper function upstream
  Equalities u == Equalities u' = u == (unsafeCoerce u')

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
fromEqual x y = fst (equal empty x y)

-- TODO? Add inequality keys? Would require type-level name for Equalities.
type Find :: (k -> Type) -> k -> Type
data Find f x
  = Find
    { -- | The value of the root node
      findValue :: f x
    }

fromFind ::
  UF.Find u ann f x ->
  Find f x
fromFind f = Find (BaseUF.annVal (UF.findValue f))

equal ::
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  (Equalities f, Find f x)
equal (Equalities u) x y =
  let fx = UF.insert u x UF.emptyKeySet in
  let fy = UF.insert (UF.findUnionFind fx) y UF.emptyKeySet in
  let (u', f) = UF.unionByKey (UF.findUnionFind fy) (UF.findKey fx) (UF.findKey fy) in
  (Equalities u', fromFind f)

notEqual ::
  EqF f =>
  OrdF f =>
  Equalities f ->
  f x ->
  f x ->
  Maybe (Equalities f)
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
        , basisInequations = ineqs
        }
      )

toBasis :: (EqF f, OrdF f) => Equalities f -> Basis f
toBasis = snd . basis
{-# INLINE toBasis #-}

ppBasisEqs :: (EqF f, OrdF f, ShowF f) => Basis f -> [PP.Doc ann]
ppBasisEqs b =
  map PP.pretty (basisEquations b) ++ map PP.pretty (basisInequations b)

and ::
  (EqF f, OrdF f) =>
  Equalities f ->
  Equalities f ->
  Maybe (Equalities f)
and x y =
  let b = toBasis y
      x' = foldr (\(Equation lhs rhs) es -> fst (equal es lhs rhs)) x (basisEquations b)
  in foldM (\es (Inequation lhs rhs) -> notEqual es lhs rhs) x' (basisInequations b)
