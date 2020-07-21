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
instance. We will be using an example from the first page of Donald Knuth's _The
Art Of Computer Programming, Volume 4, Fascicle 6: Satisfiability_:

```
F(p, q, r) = (p | !q) & (q | r) & (!p | !r) & (!p | !q | r)
```

We will use What4 to:
  * generate fresh constants for the three variables `p`, `q`, and `r`
  * construct an expression for `F`
  * assert that expression to our backend solver
  * ask the solver for a satisfying instance.

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

Before continuing, we will set up some global configuration for Z3:

```
  extendConfig z3Options (getConfiguration sym)
```

Next, we declare _fresh constants_ for each of our propositional variables:

```
  p <- freshConstant sym (safeSymbol "p") BaseBoolRepr
  q <- freshConstant sym (safeSymbol "q") BaseBoolRepr
  r <- freshConstant sym (safeSymbol "r") BaseBoolRepr
```

Next, we create expressions for their negation:

```
  not_p <- notPred sym p
  not_q <- notPred sym q
  not_r <- notPred sym r
```

Next, we build up each clause of `F` individually:

```
  clause1 <- orPred sym p not_q
  clause2 <- orPred sym q r
  clause3 <- orPred sym not_p not_r
  clause4 <- orPred sym not_p =<< orPred sym not_q r
```

Finally, we can create `F` out of the conjunction of these four clauses:

```
  f <- andPred sym clause1 =<<
       andPred sym clause2 =<<
       andPred sym clause3 clause4
```

Finally, we assert `f` to the backend solver (Z3, in this example), and ask for
a satisfying instance:

```
  -- Determine if f is satisfiable, and print the instance if one is found.
  checkModel sym f [ ("p", Some p)
                   , ("q", Some q)
                   , ("r", Some r)
                   ]
```

(The `checkModel` function is not a What4 function; its definition is provided
below.)

Now, let's add one more clause to `F` which will make it unsatisfiable:

```
  -- Now, let's add one more clause to f.
  clause5 <- orPred sym p =<< orPred sym q not_r
  g <- andPred sym f clause5
```

And, let's ask the solver for a satisfying instance:

```
  checkModel sym g [ ("p", Some p)
                   , ("q", Some q)
                   , ("r", Some r)
                   ]
```

This concludes the definition of our `main` function. The definition for
`checkModel` is as follows:

```
-- | Determine whether a predicate is satisfiable, and print out the values of a
-- set of expressions if a satisfying instance is found.
checkModel :: ExprBuilder sym st fs
           -> BoolExpr sym
           -> [(String, Some (Expr sym))]
           -> IO ()
checkModel sym f es = do
  -- We will use z3 to determine if f is satisfiable.
  withZ3 sym z3 defaultLogData $ \session -> do
    -- Assume f is true.
    assume (sessionWriter session) f
    runCheckSat session $ \result ->
      case result of
        Sat (ge, _) -> do
          putStrLn "Satisfiable, with model:"
          forM_ es $ \(nm, Some e) -> do
            v <- groundEval ge e
            putStrLn $ "  " ++ nm ++ " := " ++ showGV (exprType e) v
        Unsat _ -> putStrLn "Unsatisfiable."
        Unknown -> putStrLn "Solver failed to find a solution."
  where showGV :: BaseTypeRepr tp -> GroundValue tp -> String
        showGV tp v = case tp of
          BaseBoolRepr -> show v
          _ -> "<..>"
```

If we compile this code and run it, we get the following output:

```
Satisfiable, with model:
  p := False
  q := False
  r := True
Unsatisfiable.
```

## Where to go next

The key modules to look at when modeling a problem with What4 are:

* `What4.BaseTypes` (the datatypes What4 understands)
* `What4.Interface` (the functions What4 uses to build symbolic expressions)
* `What4.Expr.Builder` (the implementation of the functions in `What4.Interface`)

The key modules to look at when interacting with a solver are:

* `What4.Protocol.SMTLib2` (the functions to interact with a solver backend)
* `What4.Solver` (solver-specific implementations of `What4.Protocol.SMTLib2`)
* `What4.Solver.*`
* `What4.SatResult` and `What4.Expr.GroundEval` (for analyzing solver output)
