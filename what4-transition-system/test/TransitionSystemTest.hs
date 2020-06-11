{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : TransitionSystemTest
-- Copyright   : (c) Galois Inc, 2020
-- License     : BSD3
-- Maintainer  : valentin.robert.42@gmail.com
-- |
module Main where

import qualified Control.Lens as L
import Control.Monad (join)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Nonce
-- import Data.Parameterized.Some
-- import Data.Parameterized.TraversableFC
-- import qualified Data.Set as Set
-- import Data.Text (Text)
-- import qualified Data.Text.Lazy as Lazy
-- import qualified Data.Text.Lazy.Builder as Builder
import Language.Sally
import Language.Sally.Writer
import qualified System.IO.Streams as Streams
-- import qualified Text.PrettyPrint.ANSI.Leijen as PP
import What4.BaseTypes
import What4.Expr
import What4.Expr.Builder
import qualified What4.Interface as What4
-- import What4.ProblemFeatures
-- import What4.Protocol.SMTLib2 hiding (newWriter)
-- import What4.Protocol.SMTLib2.Syntax as SMT2
import What4.Protocol.SMTWriter as SMTWriter
import What4.Solver.Adapter
import What4.TransitionSystem
import Prelude hiding (init)

showBinding :: SymbolBinding t -> String
showBinding (VarSymbolBinding x) = show x
showBinding (FnSymbolBinding x) = show x

displayTransitionSystem ::
  sym ~ ExprBuilder t st fs =>
  sym ->
  TransitionSystem sym stateFields ->
  IO ()
displayTransitionSystem sym transitionSystem =
  do
    sts <- transitionSystemToSally sym mySallyNames transitionSystem
    sexp <- sexpOfTrResult sym sts
    print . sxPretty $ sexp

main :: IO ()
main =
  do
    withIONonceGenerator $ \nonceGen -> do
      sym <- newExprBuilder FloatIEEERepr State nonceGen
      ts <- counterTransitionSystem sym
      displayTransitionSystem sym ts
    withIONonceGenerator $ \nonceGen -> do
      sym <- newExprBuilder FloatIEEERepr State nonceGen
      ts <- realsTransitionSystem sym
      displayTransitionSystem sym ts

-- We don't need any information in the state
data State t = State

makeFieldNames ::
  forall stateType.
  [What4.SolverSymbol] ->
  Ctx.Assignment BaseTypeRepr stateType ->
  Ctx.Assignment (L.Const What4.SolverSymbol) stateType
makeFieldNames fields rep = Ctx.generate (Ctx.size rep) generator
  where
    generator :: Ctx.Index stateType tp -> L.Const What4.SolverSymbol tp
    generator index = L.Const (fields !! (Ctx.indexVal index))

--
-- Example 1: a simple counter
--
type CounterStateType = Ctx.EmptyCtx Ctx.::> BaseBoolType Ctx.::> BaseNatType

counterStateFields :: [What4.SolverSymbol]
counterStateFields = userSymbol' <$> ["counterIsEven", "counter"]

counterFieldNames :: Ctx.Assignment (L.Const What4.SolverSymbol) CounterStateType
counterFieldNames = makeFieldNames counterStateFields knownRepr

counterIsEven :: Ctx.Index CounterStateType BaseBoolType
counterIsEven = Ctx.natIndex @0

counter :: Ctx.Index CounterStateType BaseNatType
counter = Ctx.natIndex @1

-- | Example initial state predicate, this one constrains the `bool` field to be
-- true, and the `nat` field to be equal to zero
counterInitial ::
  What4.IsSymExprBuilder sym =>
  sym ->
  -- | mapping to a variable for each state field
  What4.SymStruct sym CounterStateType ->
  IO (What4.Pred sym)
counterInitial sym init =
  do
    initCounterIsEven <- What4.structField sym init counterIsEven
    initCounter <- What4.structField sym init counter
    nZero <- What4.natLit sym 0
    natCond <- What4.natEq sym initCounter nZero
    andCond <- What4.andPred sym initCounterIsEven natCond
    return andCond

-- | Example state transition, here, during a transition, the boolean gets
-- negated, and the natural number gets incremented.  One property of such a
-- system would be that when the boolean is false, the number is even (assuming
-- a false and zero initial state).
counterTransitions ::
  What4.IsSymExprBuilder sym =>
  sym ->
  -- | current state
  What4.SymStruct sym CounterStateType ->
  -- | next state
  What4.SymStruct sym CounterStateType ->
  IO [(String, What4.Pred sym)]
counterTransitions sym state next =
  do
    stateCounterIsEven <- What4.structField sym state counterIsEven
    stateCounter <- What4.structField sym state counter
    nextCounterIsEven <- What4.structField sym next counterIsEven
    nextCounter <- What4.structField sym next counter
    -- (= next.counter (+ 1 state.counter))
    nOne <- What4.natLit sym 1
    nStatePlusOne <- What4.natAdd sym nOne stateCounter
    natCond <- What4.natEq sym nextCounter nStatePlusOne
    -- (= next.counterIsEven (not state.counterIsEven))
    bStateNeg <- What4.notPred sym stateCounterIsEven
    boolCond <- What4.eqPred sym nextCounterIsEven bStateNeg
    andCond <- What4.andPred sym boolCond natCond
    return [("CounterTransition", andCond)]

-- | TODO
counterTransitionSystem ::
  ExprBuilder t st fs ->
  IO (TransitionSystem (ExprBuilder t st fs) CounterStateType)
counterTransitionSystem sym =
  do
    return $
      TransitionSystem
        { stateFieldsRepr = knownRepr,
          stateFieldsNames = counterFieldNames,
          initialStatePred = counterInitial sym,
          stateTransitions = counterTransitions sym,
          queries = pure []
        }

--
-- Example 2: using real numbers
--

-- based on sally/test/regress/bmc/nra/algebraic.mcmt

type RealsStateType =
  Ctx.EmptyCtx
    Ctx.::> BaseRealType
    Ctx.::> BaseRealType
    Ctx.::> BaseRealType

realsStateFields :: [What4.SolverSymbol]
realsStateFields = userSymbol' <$> ["P", "x", "n"]

realsFieldNames :: Ctx.Assignment (L.Const What4.SolverSymbol) RealsStateType
realsFieldNames = makeFieldNames realsStateFields knownRepr

pReals :: Ctx.Index RealsStateType BaseRealType
pReals = Ctx.natIndex @0

xReals :: Ctx.Index RealsStateType BaseRealType
xReals = Ctx.natIndex @1

nReals :: Ctx.Index RealsStateType BaseRealType
nReals = Ctx.natIndex @2

realsInitial ::
  What4.IsSymExprBuilder sym =>
  sym ->
  -- | mapping to a variable for each state field
  What4.SymStruct sym RealsStateType ->
  IO (What4.Pred sym)
realsInitial sym init =
  do
    pInit <- What4.structField sym init pReals
    nInit <- What4.structField sym init nReals
    -- (and (= P 1) (= n 0))
    join
      ( What4.andPred sym
          <$> (What4.realEq sym pInit =<< What4.realLit sym 1)
          <*> (What4.realEq sym nInit =<< What4.realLit sym 0)
      )

realsTransitions ::
  What4.IsSymExprBuilder sym =>
  sym ->
  -- | current state
  What4.SymStruct sym RealsStateType ->
  -- | next state
  What4.SymStruct sym RealsStateType ->
  IO [(String, What4.Pred sym)]
realsTransitions sym state next =
  do
    pState <- What4.structField sym state pReals
    xState <- What4.structField sym state xReals
    nState <- What4.structField sym state nReals
    pNext <- What4.structField sym next pReals
    xNext <- What4.structField sym next xReals
    nNext <- What4.structField sym next nReals
    -- (= next.P (* state.P state.x)
    c1 <- join $ What4.realEq sym pNext <$> What4.realMul sym pState xState
    -- (= next.n (+ state.n 1))
    c2 <- join $ What4.realEq sym nNext <$> (What4.realAdd sym nState =<< What4.realLit sym 1)
    -- (= next.x state.x)
    c3 <- What4.realEq sym xNext xState
    t <- What4.andPred sym c1 =<< What4.andPred sym c2 c3
    return [("RealsTransition", t)]

-- | TODO
realsTransitionSystem ::
  ExprBuilder t st fs ->
  IO (TransitionSystem (ExprBuilder t st fs) RealsStateType)
realsTransitionSystem sym =
  do
    return $
      TransitionSystem
        { stateFieldsRepr = knownRepr,
          stateFieldsNames = realsFieldNames,
          initialStatePred = realsInitial sym,
          stateTransitions = realsTransitions sym,
          queries = pure []
        }
