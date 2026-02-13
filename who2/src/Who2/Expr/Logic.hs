{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Who2.Expr.Logic
  ( LogicExpr(..)
  , BoolExprWrapper(..)
  , pretty
  ) where

import Data.Kind (Type)

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.TH.GADT as PTH
import qualified Prettyprinter as PP

import           Data.Parameterized.NatRepr (type (<=), NatRepr)

import qualified What4.BaseTypes as BT

import Who2.Expr (HasBaseType(baseType))
import qualified Who2.Expr as E
import qualified Who2.Expr.Bloom.Polarized as PBS
import qualified Who2.Expr.Views as EV

-- | 'Polarizable' wrapper for boolean expressions used in both 'AndPred' and 'OrPred'
newtype BoolExprWrapper f = BoolExprWrapper { unBoolExprWrapper :: f BT.BaseBoolType }
deriving instance Eq (f BT.BaseBoolType) => Eq (BoolExprWrapper f)
deriving instance Ord (f BT.BaseBoolType) => Ord (BoolExprWrapper f)
deriving instance Show (f BT.BaseBoolType) => Show (BoolExprWrapper f)

instance (Eq (f BT.BaseBoolType), PC.HashableF f) => PC.Hashable (BoolExprWrapper f) where
  hashWithSalt s (BoolExprWrapper expr) = PC.hashWithSaltF s expr

instance EV.HasLogicViews f => PBS.Polarizable (BoolExprWrapper (E.Expr t f)) where
  polarity (BoolExprWrapper expr) = case EV.asNotPred expr of
    Just inner -> PBS.Negative (BoolExprWrapper inner)
    Nothing -> PBS.Positive (BoolExprWrapper expr)
  {-# INLINE polarity #-}

data LogicExpr (f :: BT.BaseType -> Type) (tp :: BT.BaseType) where
  TruePred :: LogicExpr f BT.BaseBoolType
  FalsePred :: LogicExpr f BT.BaseBoolType

  EqPred ::
    !(f tp) ->
    !(f tp) ->
    LogicExpr f BT.BaseBoolType

  AndPred :: !(PBS.PolarizedBloomSeq (BoolExprWrapper f)) -> LogicExpr f BT.BaseBoolType

  NotPred ::
    !(f BT.BaseBoolType) ->
    LogicExpr f BT.BaseBoolType

  OrPred :: !(PBS.PolarizedBloomSeq (BoolExprWrapper f)) -> LogicExpr f BT.BaseBoolType

  Ite ::
    !(f BT.BaseBoolType) ->
    !(f tp) ->
    !(f tp) ->
    LogicExpr f tp

  BVUlt ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    LogicExpr f BT.BaseBoolType

  BVUle ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    LogicExpr f BT.BaseBoolType

  BVSlt ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    LogicExpr f BT.BaseBoolType

  BVSle ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(f (BT.BaseBVType w)) ->
    !(f (BT.BaseBVType w)) ->
    LogicExpr f BT.BaseBoolType

instance HasBaseType f => HasBaseType (LogicExpr f) where
  baseType =
    \case
      TruePred -> BT.BaseBoolRepr
      FalsePred -> BT.BaseBoolRepr
      EqPred _ _ -> BT.BaseBoolRepr
      AndPred _ -> BT.BaseBoolRepr
      NotPred _ -> BT.BaseBoolRepr
      OrPred _ -> BT.BaseBoolRepr
      Ite _ t _ -> baseType t
      BVUlt {} -> BT.BaseBoolRepr
      BVUle {} -> BT.BaseBoolRepr
      BVSlt {} -> BT.BaseBoolRepr
      BVSle {} -> BT.BaseBoolRepr

$(return [])

instance (PC.TestEquality f) => PC.TestEquality (LogicExpr f) where
  testEquality =
    $(PTH.structuralTypeEquality
       [t|LogicExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.testEquality|])
       , (PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType, [|PC.testEquality|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BoolExprWrapper|] `PTH.TypeApp` PTH.AnyType), [|\x y -> if PBS.eqBy (\(BoolExprWrapper u) (BoolExprWrapper v) -> PC.isJust (PC.testEquality u v)) x y then Just PC.Refl else Nothing|])
       ]
     )

instance (PC.OrdF f, Ord (f BT.BaseBoolType)) => PC.OrdF (LogicExpr f) where
  compareF =
    $(PTH.structuralTypeOrd
       [t|LogicExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.compareF|])
       , (PTH.ConType [t|NatRepr|] `PTH.TypeApp` PTH.AnyType, [|PC.compareF|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` (PTH.ConType [t|BoolExprWrapper|] `PTH.TypeApp` PTH.AnyType), [|\pbs1 pbs2 -> PC.fromOrdering (PBS.ordBy (\(BoolExprWrapper u) (BoolExprWrapper v) -> compare u v) pbs1 pbs2)|])
       ]
     )

instance (PC.HashableF f, Eq (f BT.BaseBoolType), PC.Hashable (f BT.BaseBoolType)) => PC.HashableF (LogicExpr f) where
  hashWithSaltF =
    $(PTH.structuralHashWithSalt
       [t|LogicExpr|]
       [ (PTH.DataArg 0 `PTH.TypeApp` PTH.AnyType, [|PC.hashWithSaltF|])
       , (PTH.ConType [t|PBS.PolarizedBloomSeq|] `PTH.TypeApp` PTH.ConType [t|BoolExprWrapper|], [|\s pbs -> PBS.hashPBSWith (\s' (BoolExprWrapper e) -> PC.hashWithSaltF s' e) s pbs|])
       ]
     )

-- | Pretty-print a logic expression given a pretty-printer for the term functor
pretty :: (forall tp'. f tp' -> PP.Doc ann) -> LogicExpr f tp -> PP.Doc ann
pretty ppF = \case
  TruePred -> PP.pretty "true"
  FalsePred -> PP.pretty "false"
  EqPred x y -> PP.parens $ PP.pretty "=" PP.<+> ppF x PP.<+> ppF y
  AndPred _pbs -> PP.pretty "and"
  NotPred x -> PP.parens $ PP.pretty "not" PP.<+> ppF x
  OrPred _pbs -> PP.pretty "or"
  Ite c t f -> PP.parens $ PP.pretty "ite" PP.<+> ppF c PP.<+> ppF t PP.<+> ppF f
  BVUlt _w x y -> PP.parens $ PP.pretty "bvult" PP.<+> ppF x PP.<+> ppF y
  BVUle _w x y -> PP.parens $ PP.pretty "bvule" PP.<+> ppF x PP.<+> ppF y
  BVSlt _w x y -> PP.parens $ PP.pretty "bvslt" PP.<+> ppF x PP.<+> ppF y
  BVSle _w x y -> PP.parens $ PP.pretty "bvsle" PP.<+> ppF x PP.<+> ppF y
