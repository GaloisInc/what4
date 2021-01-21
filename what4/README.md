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
instance.  The code for this quick start may be found in
`doc/QuickStart.hs`, and you can compile and run the quickstart
by executing the following line at the command line from the
source root of this package.

```
$ cabal v2-run what4:quickstart
```

We will be using an example from the first page of Donald Knuth's _The
Art Of Computer Programming, Volume 4, Fascicle 6: Satisfiability_:

```
F(p, q, r) = (p | !q) & (q | r) & (!p | !r) & (!p | !q | r)
```

We will use What4 to:
  * generate fresh constants for the three variables `p`, `q`, and `r`
  * construct an expression for `F`
  * assert that expression to our backend solver
  * ask the solver for a satisfying instance.

We first enable the `GADTs` extension (necessary for most
uses of What4) and pull
in a number of modules from What4 and `parameterized-utils`:

```
{-# LANGUAGE GADTs #-}
module Main where

import Data.Foldable (forM_)
import System.IO (FilePath)

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))

import What4.Config (extendConfig)
import What4.Expr
         ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
         , BoolExpr, GroundValue, groundEval )
import What4.Interface
         ( BaseTypeRepr(..), getConfiguration
         , freshConstant, safeSymbol
         , notPred, orPred, andPred )
import What4.Solver
         (defaultLogData, z3Options, withZ3, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat)
```

We create a trivial data type for the "builder state" (which we won't need to
use for this simple example), and create a top-level constant pointing
to our backend solver, which is Z3 in this example.
(To run this code, you'll need Z3 on your path, or edit this path to
point to your Z3.)

```
data BuilderState st = EmptyState

z3executable :: FilePath
z3executable = "z3"
```

We're ready to start our `main` function:

```
main :: IO ()
main = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyState ng
```

Most of the functions in `What4.Interface`, the module for building up
solver expressions, require an explicit `sym` parameter. This
parameter is a handle for a data structure that caches information for
sharing common subexpressions and other bookkeeping
purposes. `What4.Expr.Builder.newExprBuilder` creates one of these,
and we will use this `sym` throughout our code.

Before continuing, we will set up some global configuration for Z3.
This sets up some configurable options specific to Z3 with default values.

```
  extendConfig z3Options (getConfiguration sym)
```

We declare _fresh constants_ for each of our propositional variables.

```
  p <- freshConstant sym (safeSymbol "p") BaseBoolRepr
  q <- freshConstant sym (safeSymbol "q") BaseBoolRepr
  r <- freshConstant sym (safeSymbol "r") BaseBoolRepr
```

Next, we create expressions for their negation.

```
  not_p <- notPred sym p
  not_q <- notPred sym q
  not_r <- notPred sym r
```

Then, we build up each clause of `F` individually.

```
  clause1 <- orPred sym p not_q
  clause2 <- orPred sym q r
  clause3 <- orPred sym not_p not_r
  clause4 <- orPred sym not_p =<< orPred sym not_q r
```

Finally, we can create `F` out of the conjunction of these four clauses.

```
  f <- andPred sym clause1 =<<
       andPred sym clause2 =<<
       andPred sym clause3 clause4
```

Now we can we assert `f` to the backend solver (Z3, in this example), and ask for
a satisfying instance.

```
  -- Determine if f is satisfiable, and print the instance if one is found.
  checkModel sym f [ ("p", p)
                   , ("q", q)
                   , ("r", r)
                   ]
```

(The `checkModel` function is not a What4 function; its definition is provided
below.)

Now, let's add one more clause to `F` which will make it unsatisfiable.

```
  -- Now, let's add one more clause to f.
  clause5 <- orPred sym p =<< orPred sym q not_r
  g <- andPred sym f clause5
```

Now, when we ask the solver for a satisfying instance, it should
report that the formulat is unsatisfiable.

```
  checkModel sym g [ ("p", p)
                   , ("q", q)
                   , ("r", r)
                   ]
```

This concludes the definition of our `main` function. The definition for
`checkModel` is as follows:

```
-- | Determine whether a predicate is satisfiable, and print out the values of a
-- set of expressions if a satisfying instance is found.
checkModel ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, BoolExpr t)] ->
  IO ()
checkModel sym f es = do
  -- We will use z3 to determine if f is satisfiable.
  withZ3 sym z3executable defaultLogData $ \session -> do
    -- Assume f is true.
    assume (sessionWriter session) f
    runCheckSat session $ \result ->
      case result of
        Sat (ge, _) -> do
          putStrLn "Satisfiable, with model:"
          forM_ es $ \(nm, e) -> do
            v <- groundEval ge e
            putStrLn $ "  " ++ nm ++ " := " ++ show v
        Unsat _ -> putStrLn "Unsatisfiable."
        Unknown -> putStrLn "Solver failed to find a solution."
```

When we compile this code and run it, we should get the following output.

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

Additional implementation and operational documentation can be found
in the [implementation documentation in doc/implementation.md](doc/implementation.md).

## Known working solver versions

What4 has been tested and is known to work with the following solver versions.

Nearby versions may also work; however, subtle changes in solver behavior from
version to version sometimes happen and can cause unexpected results, especially
for the more experimental logics that have not been standardized. If you
encounter such a situation, please open a ticket, as our goal is to work correctly
on as wide a collection of solvers as is reasonable.

- Z3 versions 4.8.7 and 4.8.8
- Yices 2.6.1 and 2.6.2
- CVC4 1.7 and 1.8
- Boolector 3.2.1
- STP 2.3.3
    (However, note https://github.com/stp/stp/issues/363, which prevents
    effective retrieval of model values.  This should be resolved by the next release)
- dReal v4.20.04.1

Note that the integration with Z3, Yices and CVC4 has undergone significantly
more testing than the other solvers.

