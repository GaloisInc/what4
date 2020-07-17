# What4

## Introduction

### What is What4?

What4 is a Haskell library developed at Galois that presents a generic interface
to SMT solvers (Z3, Yices, etc.). Users of What4 use an embedded DSL to create
_fresh constants_ representing unknown values of various types (integer,
boolean, etc.), assert various properties about those constants, and ask a
locally-installed SMT solver for satisfying instances.

What4 relies heavily on advanced GHC extensions to ensure that solver
expressions are type correct. The `parameterized-utils` library is used
throughout What4 as a "standard library" for dependently-typed Haskell.

## Quick start

Let's start with a quick end-to-end tutorial, demonstrating how to create a
model for a basic satisfiability problem and ask a solver for a satisfying
instance. We will be using an example from the first page of Knuth's _The Art Of
Computer Programming, Volume 4, Fascicle 6: Satisfiability_:

```
F(p, q, r) = (p | !q) & (q | r) & (!p | !r) & (!p | !q | r)
```

We will use What4 to generate fresh constants for the three variables `p`, `q`,
and `r`, to construct an expression for `F`, to assert that expression to our
backend solver, and to ask the solver for a satisfying instance.

In a file called `QuickStart.hs`, we first enable the `GADTs` extension and pull
in a number of modules from What4 and `parameterized-utils`:

```
{-# LANGUAGE GADTs #-}

module Main where

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))
import What4.Expr.Builder ( ExprBuilder
                          , Expr
                          , BoolExpr
                          , FloatModeRepr(..)
                          , newExprBuilder
                          , exprType
                          )
import What4.Config (extendConfig)
import What4.Expr.GroundEval (GroundValue, groundEval)
import What4.Interface ( getConfiguration
                       , freshConstant
                       , safeSymbol
                       , notPred
                       , orPred
                       , andPred
                       )
import What4.Protocol.SMTLib2 (assume, sessionWriter, runCheckSat)
import What4.SatResult (SatResult(..))
import What4.Solver (defaultLogData)
import What4.Solver.Z3 (z3Options, withZ3)
import What4.BaseTypes (BaseTypeRepr(..))

import Data.Foldable (forM_)
import System.IO (FilePath)
```

We create an empty data type for the "builder state" (which we won't need to
use), and create a top-level constant pointing to our backend solver, which is
Z3 in this example. (To run this code, you'll need Z3 on your path.)

```
data BuilderState st = EmptyState

z3 :: FilePath
z3 = "z3"
```

We're ready to start our `main` function:

```
main :: IO ()
main = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyState ng
```

Most of the functions in `What4.Interface`, the module for building up solver
expressions, requires an explicit `sym` parameter. This parameter is a handle
for a data structure that caches information for sharing common subexpressions.
`What4.Expr.Builder.newExprBuilder` creates one of these, and we will use this
`sym` throughout our code.
