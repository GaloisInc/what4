{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}

module What4.ExprEqualities
  ( ExprEqualities
  , Result(..)
  , empty
  , fromEqual
  , equal
  , notEqual
  , traverseExprEqualities
  , and
  , toBasis
  ) where

import Data.Coerce (coerce)
import Data.Parameterized.Classes
import Prelude hiding (and)
import qualified What4.Interface as WI
import qualified What4.Equalities as Eqs
import qualified What4.Utils.AbstractDomains as WA

newtype ExprEqualities f
  = ExprEqualities { _getEqualities :: Eqs.Equalities f }
  deriving (Eq, Hashable)

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
fromEqual = equal empty

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
{-# INLINE definitelyEqual #-}

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
{-# INLINE definitelyNotEqual #-}

equal ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  ExprEqualities f ->
  f x ->
  f x ->
  Result f
equal (ExprEqualities e) x y
 | definitelyEqual x y = ResTrue
 | definitelyNotEqual x y = ResFalse
 | otherwise =
   let (e', Eqs.findValue -> root) = Eqs.equal e x y in
   if definitelyNotEqual x root || definitelyNotEqual y root
   then ResFalse
   else Equalities (ExprEqualities e')
 -- TODO: Check for incompatibilities with inequalities? Would be O(n)

notEqual ::
  EqF f =>
  OrdF f =>
  WI.IsExpr f =>
  ExprEqualities f ->
  f x ->
  f x ->
  Result f
notEqual (ExprEqualities e) x y
 | definitelyEqual x y = ResFalse
 | definitelyNotEqual x y = ResTrue
 | otherwise = Equalities (ExprEqualities (Eqs.notEqual e x y))
 -- TODO: Check for incompatibilities with inequalities? Would be O(n)

traverseExprEqualities ::
  Applicative m =>
  EqF g =>
  OrdF g =>
  (forall x. f x -> m (g x)) ->
  ExprEqualities f ->
  m (ExprEqualities g)
traverseExprEqualities f (ExprEqualities e) =
  ExprEqualities <$> Eqs.traverseEqualities f e

and :: (EqF f, OrdF f) => ExprEqualities f -> ExprEqualities f -> ExprEqualities f
and = coerce Eqs.and
{-# INLINE and #-}

toBasis :: (EqF f, OrdF f) => ExprEqualities f -> Eqs.Basis f
toBasis = coerce Eqs.toBasis
{-# INLINE toBasis #-}
