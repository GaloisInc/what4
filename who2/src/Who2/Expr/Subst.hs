{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Expr.Subst
  ( SomeExpr(..)
  , substituteBoundVars
  , substBoundVarsInFn
  ) where

import           Control.Monad (foldM)
import qualified Data.BitVector.Sized as BV
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Nonce as Nonce
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (toListFC)

import qualified What4.BaseTypes as BT
import qualified What4.Expr as WE
import qualified What4.Expr.App as WEA
import qualified What4.Interface as WI

import qualified Who2.Expr as E
import qualified Who2.Expr.App as EA
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.Bloom.Polarized as PBS
import qualified Who2.Expr.SymExpr as ESE
import qualified Who2.Expr.SymFn as ESF
import qualified Who2.Expr.Bloom.SemiRing.Product as SRP
import qualified Who2.Expr.Bloom.SemiRing.Sum as SRS
import qualified Who2.Expr.HashConsed.Polarized as PES
import qualified Who2.Expr.HashConsed.SemiRing.Sum as HCSR
import qualified Who2.Expr.HashConsed.SemiRing.Product as HCPR

-- | Existential wrapper for expressions with hidden type parameter
data SomeExpr t = forall tp. SomeExpr (E.Expr t (EA.App t) tp)

-- | Substitute bound variables with expressions
-- Used for beta reduction in defined functions
substituteBoundVars ::
  forall sym t ret.
  ( WI.IsSymExprBuilder sym
  , WI.SymExpr sym ~ ESE.SymExpr t
  , WI.SymFn sym ~ ESF.SymFn t (E.Expr t (EA.App t))
  ) =>
  sym ->
  E.Expr t (EA.App t) ret ->
  IntMap.IntMap (SomeExpr t) ->  -- Nonce index -> replacement expression
  IO (E.Expr t (EA.App t) ret)
substituteBoundVars sym = go
  where
    go :: forall ret'. E.Expr t (EA.App t) ret' -> IntMap.IntMap (SomeExpr t) -> IO (E.Expr t (EA.App t) ret')
    go expr substMap =
      case E.eApp expr of
        -- Base case: If this is a bound variable, look it up in the substitution map
        EA.BoundVarApp bvar ->
          case IntMap.lookup (fromIntegral $ Nonce.indexValue $ WEA.bvarId bvar) substMap of
            Just (SomeExpr replacement) ->
              -- Found a substitution - need to verify types match
              case PC.testEquality (E.baseType expr) (E.baseType replacement) of
                Just PC.Refl -> return replacement
                Nothing -> error "substituteBoundVars: type mismatch in substitution"
            Nothing ->
              -- No substitution for this variable (it's free in this context)
              return expr

        -- Bitvector operations: traverse and rebuild using builder methods
        EA.BVApp bvExpr -> substInBVExpr bvExpr substMap

        -- Logic operations: traverse and rebuild using builder methods
        EA.LogicApp logicExpr -> substInLogicExpr logicExpr substMap

        -- Function application: substitute arguments, then apply
        -- This may trigger nested unfolding if the function is also defined
        EA.FnApp fn args -> do
          args' <- Ctx.traverseWithIndex (\_ e -> ESE.SymExpr <$> go e substMap) args
          ESE.getSymExpr <$> WI.applySymFn sym fn args'

    -- Helper to wrap/unwrap for binary operations
    binOp :: (WI.SymExpr sym tp1 -> WI.SymExpr sym tp2 -> IO (WI.SymExpr sym tp3))
          -> E.Expr t (EA.App t) tp1
          -> E.Expr t (EA.App t) tp2
          -> IO (E.Expr t (EA.App t) tp3)
    binOp f e1 e2 = ESE.getSymExpr <$> f (ESE.SymExpr e1) (ESE.SymExpr e2)

    unOp :: (WI.SymExpr sym tp1 -> IO (WI.SymExpr sym tp2))
         -> E.Expr t (EA.App t) tp1
         -> IO (E.Expr t (EA.App t) tp2)
    unOp f e = ESE.getSymExpr <$> f (ESE.SymExpr e)

    -- Substitute in bitvector expressions using IsExprBuilder methods
    substInBVExpr :: forall tp. EBV.BVExpr (E.Expr t (EA.App t)) tp -> IntMap.IntMap (SomeExpr t) -> IO (E.Expr t (EA.App t) tp)
    substInBVExpr bvExpr substMap = case bvExpr of
      EBV.BVLit w bv -> ESE.getSymExpr <$> WI.bvLit sym w bv
      EBV.BVNeg _w e -> go e substMap >>= unOp (WI.bvNeg sym)
      EBV.BVAdd w ws -> do
        -- Substitute in all terms of the weighted sum, then add them back
        let terms = SRS.toTerms ws
            offset = SRS.sumOffset ws
        -- Start with the offset
        result <- if offset == BV.zero w
                  then ESE.getSymExpr <$> WI.bvZero sym w
                  else ESE.getSymExpr <$> WI.bvLit sym w offset
        -- Add each term
        foldM (\acc (term, coeff) -> do
                 term' <- go term substMap
                 scaledTerm <- if coeff == BV.mkBV w 1
                               then return term'
                               else do
                                 coeffExpr <- ESE.getSymExpr <$> WI.bvLit sym w coeff
                                 ESE.getSymExpr <$> WI.bvMul sym (ESE.SymExpr term') (ESE.SymExpr coeffExpr)
                 ESE.getSymExpr <$> WI.bvAdd sym (ESE.SymExpr acc) (ESE.SymExpr scaledTerm))
              result
              terms
      EBV.BVSub _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvSub sym) e1' e2'
      EBV.BVMul w wp -> do
        let terms = SRP.toTerms wp
        terms' <- mapM (\(e, expn) -> do
                          e' <- go e substMap
                          return (e', expn)) terms
        let expandedTerms = concatMap (\(e', expn) -> replicate (fromIntegral expn) e') terms'
        case expandedTerms of
          [] -> ESE.getSymExpr <$> WI.bvOne sym w
          (t:ts) -> foldM (\acc x -> binOp (WI.bvMul sym) acc x) t ts
      EBV.BVUdiv _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvUdiv sym) e1' e2'
      EBV.BVUrem _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvUrem sym) e1' e2'
      EBV.BVSdiv _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvSdiv sym) e1' e2'
      EBV.BVSrem _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvSrem sym) e1' e2'
      EBV.BVAndBits w pbs -> do
        -- Fold positive elements with bvAndBits
        posElems' <- mapM ((`go` substMap) . EBV.unBVExprWrapper) (PBS.toListPos pbs)
        -- Fold negative elements (notBits applied) with bvAndBits
        negElems' <- mapM ((`go` substMap) . EBV.unBVExprWrapper) (PBS.toListNeg pbs)
        negElems'' <- mapM (unOp (WI.bvNotBits sym)) negElems'
        -- Combine all elements with bvAndBits
        case posElems' ++ negElems'' of
          [] -> ESE.getSymExpr <$> WI.bvLit sym w (BV.maxUnsigned w)
          (x:xs) -> foldM (\a b -> binOp (WI.bvAndBits sym) a b) x xs
      EBV.BVOrBits w pbs -> do
        -- Fold positive elements with bvOrBits
        posElems' <- mapM ((`go` substMap) . EBV.unBVExprWrapper) (PBS.toListPos pbs)
        -- Fold negative elements (notBits applied) with bvOrBits
        negElems' <- mapM ((`go` substMap) . EBV.unBVExprWrapper) (PBS.toListNeg pbs)
        negElems'' <- mapM (unOp (WI.bvNotBits sym)) negElems'
        -- Combine all elements with bvOrBits
        case posElems' ++ negElems'' of
          [] -> ESE.getSymExpr <$> WI.bvZero sym w
          (x:xs) -> foldM (\a b -> binOp (WI.bvOrBits sym) a b) x xs
      EBV.BVXorBits _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvXorBits sym) e1' e2'
      EBV.BVNotBits _w e -> go e substMap >>= unOp (WI.bvNotBits sym)
      EBV.BVShl _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvShl sym) e1' e2'
      EBV.BVLshr _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvLshr sym) e1' e2'
      EBV.BVAshr _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvAshr sym) e1' e2'
      EBV.BVZext w _w' e -> go e substMap >>= unOp (WI.bvZext sym w)
      EBV.BVSext w _w' e -> go e substMap >>= unOp (WI.bvSext sym w)
      EBV.BVConcat _w1 _w2 e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvConcat sym) e1' e2'
      EBV.BVSelect idx n _w e -> go e substMap >>= unOp (WI.bvSelect sym idx n)
      EBV.BVRol _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvRol sym) e1' e2'
      EBV.BVRor _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvRor sym) e1' e2'
      -- Hash-consed constructors
      EBV.BVAndBitsHC w pset -> do
        posElems' <- mapM (`go` substMap) (PES.toListPos pset)
        negElems' <- mapM (`go` substMap) (PES.toListNeg pset)
        negElems'' <- mapM (unOp (WI.bvNotBits sym)) negElems'
        case posElems' ++ negElems'' of
          [] -> ESE.getSymExpr <$> WI.bvLit sym w (BV.maxUnsigned w)
          (x:xs) -> foldM (\a b -> binOp (WI.bvAndBits sym) a b) x xs
      EBV.BVOrBitsHC w pset -> do
        posElems' <- mapM (`go` substMap) (PES.toListPos pset)
        negElems' <- mapM (`go` substMap) (PES.toListNeg pset)
        negElems'' <- mapM (unOp (WI.bvNotBits sym)) negElems'
        case posElems' ++ negElems'' of
          [] -> ESE.getSymExpr <$> WI.bvZero sym w
          (x:xs) -> foldM (\a b -> binOp (WI.bvOrBits sym) a b) x xs
      EBV.BVAddHC w ws -> do
        let terms = HCSR.toTerms ws
            offset = HCSR.sumOffset ws
        result <- if offset == BV.zero w
                  then ESE.getSymExpr <$> WI.bvZero sym w
                  else ESE.getSymExpr <$> WI.bvLit sym w offset
        foldM (\acc (term, coeff) -> do
                 term' <- go term substMap
                 scaledTerm <- if coeff == BV.mkBV w 1
                               then return term'
                               else do
                                 coeffExpr <- ESE.getSymExpr <$> WI.bvLit sym w coeff
                                 ESE.getSymExpr <$> WI.bvMul sym (ESE.SymExpr term') (ESE.SymExpr coeffExpr)
                 ESE.getSymExpr <$> WI.bvAdd sym (ESE.SymExpr acc) (ESE.SymExpr scaledTerm))
              result
              terms
      EBV.BVMulHC w wp -> do
        let terms = HCPR.toTerms wp
        terms' <- mapM (\(e, expn) -> do
                          e' <- go e substMap
                          return (e', expn)) terms
        let expandedTerms = concatMap (\(e', expn) -> replicate (fromIntegral expn) e') terms'
        case expandedTerms of
          [] -> ESE.getSymExpr <$> WI.bvOne sym w
          (t:ts) -> foldM (\acc x -> binOp (WI.bvMul sym) acc x) t ts

    -- Substitute in logic expressions using IsExprBuilder methods
    substInLogicExpr :: forall tp. EL.LogicExpr (E.Expr t (EA.App t)) tp -> IntMap.IntMap (SomeExpr t) -> IO (E.Expr t (EA.App t) tp)
    substInLogicExpr logicExpr substMap = case logicExpr of
      EL.TruePred -> pure $ ESE.getSymExpr (WI.truePred sym)
      EL.FalsePred -> pure $ ESE.getSymExpr (WI.falsePred sym)
      EL.NotPred e -> go e substMap >>= unOp (WI.notPred sym)
      EL.XorPred e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.xorPred sym) e1' e2'
      EL.AndPred pbs -> do
        -- Fold positive elements with andPred
        posElems' <- mapM ((`go` substMap) . EL.unBoolExprWrapper) (PBS.toListPos pbs)
        -- Fold negative elements (notPred applied) with andPred
        negElems' <- mapM ((`go` substMap) . EL.unBoolExprWrapper) (PBS.toListNeg pbs)
        negElems'' <- mapM (unOp (WI.notPred sym)) negElems'
        -- Combine all elements with andPred
        case posElems' ++ negElems'' of
          [] -> pure $ ESE.getSymExpr (WI.truePred sym)
          (x:xs) -> foldM (\a b -> binOp (WI.andPred sym) a b) x xs
      EL.OrPred pbs -> do
        -- Fold positive elements with orPred
        posElems' <- mapM ((`go` substMap) . EL.unBoolExprWrapper) (PBS.toListPos pbs)
        -- Fold negative elements (notPred applied) with orPred
        negElems' <- mapM ((`go` substMap) . EL.unBoolExprWrapper) (PBS.toListNeg pbs)
        negElems'' <- mapM (unOp (WI.notPred sym)) negElems'
        -- Combine all elements with orPred
        case posElems' ++ negElems'' of
          [] -> pure $ ESE.getSymExpr (WI.falsePred sym)
          (x:xs) -> foldM (\a b -> binOp (WI.orPred sym) a b) x xs
      EL.Ite c t f -> do
        c' <- go c substMap
        t' <- go t substMap
        f' <- go f substMap
        case E.baseType t' of
          BT.BaseBoolRepr -> ESE.getSymExpr <$> WI.itePred sym (ESE.SymExpr c') (ESE.SymExpr t') (ESE.SymExpr f')
          _ -> ESE.getSymExpr <$> WI.baseTypeIte sym (ESE.SymExpr c') (ESE.SymExpr t') (ESE.SymExpr f')
      EL.EqPred e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        case E.baseType e1' of
          BT.BaseBoolRepr -> binOp (WI.eqPred sym) e1' e2'
          BT.BaseBVRepr _w -> binOp (WI.bvEq sym) e1' e2'
          _ -> binOp (WI.isEq sym) e1' e2'
      EL.BVUle _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvUle sym) e1' e2'
      EL.BVUlt _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvUlt sym) e1' e2'
      EL.BVSle _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvSle sym) e1' e2'
      EL.BVSlt _w e1 e2 -> do
        e1' <- go e1 substMap
        e2' <- go e2 substMap
        binOp (WI.bvSlt sym) e1' e2'

-- | Helper specifically for function application (builds map from vars)
-- This is the main entry point for beta reduction in defined functions
substBoundVarsInFn ::
  ( WI.IsSymExprBuilder sym
  , WI.SymExpr sym ~ ESE.SymExpr t
  , WI.SymFn sym ~ ESF.SymFn t (E.Expr t (EA.App t))
  ) =>
  sym ->
  E.Expr t (EA.App t) ret ->
  Ctx.Assignment (WE.ExprBoundVar t) args ->
  Ctx.Assignment (E.Expr t (EA.App t)) args ->
  IO (E.Expr t (EA.App t) ret)
substBoundVarsInFn sym body vars vals = do
  let substMap = buildSubstMap vars vals
  substituteBoundVars sym body substMap
  where
    buildSubstMap :: Ctx.Assignment (WE.ExprBoundVar t) args
                  -> Ctx.Assignment (E.Expr t (EA.App t)) args
                  -> IntMap.IntMap (SomeExpr t)
    buildSubstMap vs es = IntMap.fromList
      [ (fromIntegral (Nonce.indexValue (WEA.bvarId v)), SomeExpr e)
      | (Some v, Some e) <- zip (toListFC Some vs) (toListFC Some es)
      ]
