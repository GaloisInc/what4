# next

* The `BoolMap` parameter of `ConjPred` is now a `ConjMap`.

# 1.6.2 (Sep 2024)

* Allow building with GHC 9.10.

# 1.6.1 (Sep 2024)

* Fix a bug in which `what4`'s CVC5 adapter would fail to parse models
  involving structs. ([#265](https://github.com/GaloisInc/what4/issues/265))

* Add `What4.Expr.GroundEval.groundToSym`, which allows injecting
  `GroundValue`s back into `SymExpr`s.
  ([#268](https://github.com/GaloisInc/what4/pull/268))

# 1.6 (May 2024)

* Allow building with GHC 9.8.

* Add more robust support for Constrained Horn Clause (CHC) solving:
  * The `IsSymExprBuilder` class now has two additional methods,
    `transformPredBV2LIA` and `transformSymFnLIA2BV`, which describe how to
    transform a bitvector (BV) predicate into a linear integer arithmetic (LIA)
    predicate and vice versa.
  * The `runZ3Horn` and `writeZ3HornSMT2File` functions now take an additional
    `Bool` argument. When this argument is `True`, Z3 will transform bitvector
    CHCs into linear integer arithmetic CHCs, which can sometimes help Z3 to
    solve CHC problems that it couldn't in a bitvector setting.

* Add support for the `bitwuzla` SMT solver.

* Add `bvZero` and `bvOne` functions, which are convenient shorthand for
  constructing bitvectors with the values `0` and `1`, respectively.

* Add `pushMuxOps` and `pushMuxOpsOption`. If this option is enabled, What4 will
  push certain `ExprBuilder` operations (e.g., `zext`) down to the branches of
  `ite` expressions. In some (but not all) circumstances, this can result in
  operations that are easier for SMT solvers to reason about.

* `annotateTerm` no longer adds annotations to bound variable expressions, which
  already have annotations attached to them. This should result in slightly
  better performance and better pretty-printing.

# 1.5.1 (October 2023)

* Require building with `versions >= 6.0.2`.

# 1.5 (July 2023)

* Allow building with GHC 9.6.

* The `MonadTrans (PartialT sym)` instance now has a `IsExpr (SymExpr sym)`
  constraint in its instance context. (This is a requirement imposed by
  `MonadTrans` gaining a quantified `Monad` superclass in `mtl-2.3`.)

* Make `what4` simplify expressions of the form
  `(bvult (bvadd a c) (bvadd b c))` to `(bvult a b)` when it is sound to do so.

# 1.4 (January 2023)

* Allow building with GHC 9.4.

* Remove the `MonadFail` instance for `VarRecorder`, as this instance is no
  longer straightforward to define due to upstream changes in `base-4.17.0.0`.
  This instance ultimately called `error` anyways, so any uses of `fail` at type
  `VarRecorder` can be replaced with `error` without any change in behavior.

* Remove a dependency on `data-binary-ieee754`, which has been deprecated.

* Deprecate `allSupported` which represents the SMT logic `ALL_SUPPORTED`,
  and add `allLogic` instead which represents the SMTLib standard logic `ALL`.

* Add support for the cvc5 SMT solver.

* Add a `get-abduct` feature which is compatible with cvc5.

* Add modules to support serialization and deserialization of what4 terms into
  an s-expression format that is a superset of SMTLib2. See the
  `What4.Serialize.Printer`, `What4.Serialize.Parser`, and
  `What4.Serialize.FastSExpr` modules. Note that these modules have names that
  conflict with the now deprecated what4-serialize package, from which they were
  copied. If you are updating to this version of what4, delete your dependency
  on what4-serialize.

* Add support Syntax-Guided Synthesis (SyGuS) in CVC5 (through the
  `runCVC5SyGuS` function) and Constrained Horn Clauses (CHC) in Z3 (through the
  `runZ3Horn` function).

* Make `what4` smarter about simplifying `intMin x y` and `intMax x y`
  expressions when either `x <= y` or `y <= x` can be statically determined.

# 1.3 (April 2022)

* Allow building with GHC 9.2.

* According to
  [this discussion](https://github.com/ghc-proposals/ghc-proposals/discussions/440),
  the `forall` identifier will be claimed, and `forall` made into a
  full keyword. Therefore, the `forall` and `exists` combinators of
  `What4.Protocol.SMTLib2.Syntax` have been
  renamed into `forall_` and `exists_`.

* Add operations for increased control over the scope of
  configuration options, both in the `What4.Config` and
  `What4.Expr.Builder` modules.

* Previously, the `exprCounter`, `sbUserState`, `sbUnaryThreshold`, and
  `sbCacheStartSize` fields of `ExprBuilder` were directly exposed; in
  principle this allows users to modify them, which was not intended
  in some cases.  These have been uniformly renamed to remove the `sb`
  prefix, and exposed as `Getter` or `Lens` values instead, as
  appropriate.

* The `sbBVDomainRangeLimit` fields of `ExprBuilder` was obsolete and
  has been removed.

* Allow building with `hashable-1.4.*`:
  * Add `Eq` instances for all data types with `Hashable` instances that
    were missing corresponding `Eq` instances. This is required since
    `hashable-1.4.0.0` adds an `Eq` superclass to `Hashable`.
  * Some `Hashable` instances now have extra constraints to match the
    constraints in their corresponding `Eq` instances. For example,
    the `Hashable` instance for `SymNat` now has an extra `TestEquality`
    constraint to match its `Eq` instance.

* Add an `unsafeSetAbstractValue` function to the `IsExpr` class which allows
  one to manually set the `AbstractValue` used in a symbolic expression.
  As the name suggests, this function is unsound in the general case, so use
  this with caution.

* Add a `What4.Utils.ResolveBounds.BV` module, which provides a `resolveSymBV`
  function that checks if a `SymBV` is concrete. If it is not concrete, it
  returns the lower and upper version bounds, as determined by querying an
  online SMT solver.

* Add `arrayCopy`, `arraySet`, and `arrayRangeEq` methods to `IsExprBuilder`.

* Add a `getUnannotatedTerm` method to `IsExprBuilder` for retrieving the
  original, unannotated term out of an annotated term.

* `IsExprBuilder` now has `floatSpecialFunction{,0,1,2}`
  and `realSpecialFunction{,0,1,2}` methods which allow the use of special
  values or functions such as `pi`, trigonometric functions, exponentials, or
  logarithms. Similarly, `IsInterpretedFloatExprBuilder` now has
  `iFloatSpecialFunction{,0,1,2}` methods. Although little solver support
  exists for special functions, `what4` may be able to prove properties about
  them in limited cases.
  * The `realPi`, `realLog`, `realExp`, `realSin`, `realCos`, `realTan`,
    `realSinh`, `realCosh`, `realTanh`, and `realAtan2` methods of
    `IsExprBuilder` now have default implementations in terms of
    `realSpecialFunction{,0,1,2}`.

* Add an `exprUninterpConstants` method to `IsSymExprBuilder` which returns the
  set of uninterpreted constants in a symbolic expression.

* Add a `natToIntegerPure` function which behaves like `natToInteger` but
  without using `IO`.

* `asConcrete` now supports concretizing float expressions by way of the new
  `ConcreteFloat` constructor in `ConcreteVal`.

* Add a `z3Tactic` configuration option to `What4.Solver.Z3` that allows
  specifying a custom tactic to pass to `z3`.

* `safeSymbol` now replaces exclamation marks (`!`) with underscores (`_`) so
  that the generated names are legal in Verilog.

* Add `Foldable`, `Traversable`, and `Show` instances for `LabeledPred`.

* Fix a bug in which `what4` would generate incorrect SMTLib code for array
  lookups and updates when using the CVC4 backend.

* Fix a bug in which `what4` would incorrectly attempt to configure Boolector
  3.2.2 or later.

* Fix a bug in which strings containing `\u` or ending with `\` would be
  escaped incorrectly.

# 1.2.1 (June 2021)

* Include test suite data in the Hackage tarball.

# 1.2 (June 2021)

This is primarily a bugfix release, but also adds support
for GHC 9.x

* Tweaks to the `SolverEvent` data type to remove partial
fields.

* Fix issue #126.  The shift operations of `What4.SWord` were
not correctly handling cases where the shift amount has more
bits than the word to be shifted.

* Fix issue #121. The ordering of inputs in generated Verilog files is
now more predictable. Previously, it was determined by the order the
inputs were encountered during term traversal. Now the user can provide
a list of (input, name) pairs which are declared in order. Any
additional inputs discovered during traversal will be added after these
specified inputs.

* Fix issue #113.  The `bvSliceLE` and `bvSliceBE` functions of
`What4.SWord` did not properly handle size 0 bit-vectors and
requests for 0 length slices.  They now correctly fail for slice
lengths longer than 0 on 0-length vectors, and correctly
allow 0 length slices regardless of the length of the input.

* Fix issue #103. Some of the string operations would give incorrect
results when string offsets are out-of-bounds.  The SMTLib 2.6 standard
specifies precise results for these cases, which we now implement.

* Configuration parameters relative to solvers have been renamed in a
  more consistent and heirarchical fashion; the old configuration
  parameters still work but will emit deprecation warnings when used.

  * `default_solver` --> `solver.default`
  * `abc_path` --> `solver.abc.path`
  * `boolector_path` --> `solver.boolector.path`
  * `cvc4_path` --> `solver.cvc4.path`
  * `cvc4.random-seed` --> `solver.cvc4.random-seed`
  * `cvc4_timeout` --> `solver.cvc4.timeout`
  * `dreal_path` --> `solver.dreal.path`
  * `stp_path` --> `solver.stp.path`
  * `stp.random-seed` --> `solver.stp.random-seed`
  * `yices_path` --> `solver.yices.path`
  * `yices_enable-mcsat` --> `solver.yices.enable-mcsat`
  * `yices_enable-interactive` --> `solver.yices.enable-interactive`
  * `yices_goal_timeout` --> `solver.yices.goal-timeout`
  * `yices.*` --> `solver.yices.*` for many yices internal options
  * `z3_path` --> `solver.z3.path`
  * `z3_timeout` --> `solver.z3.timeout`

* Added the `solver.strict_parsing` configuration parameter.  This is
  enabled by default but could be disabled to allow running solvers in
  debug mode or to workaround other unexpected output from solver
  processes.

# 1.1 (February 2021)

* Use multithread-safe storage primitive for configuration options,
  and clarify single-threaded use assumptions for other data structures.

* Fix issue #63, which caused traversals to include the bodies of
defined functions at call sites, which yielded confusing results.

* Add concrete evaluation and constant folding for floating-point
operations via the `libBF` library.

* Add min and max operations for integers and reals to the expression interface.

* Remove `BaseNatType` from the set of base types. There were bugs
  relating to having nat types appear in structs, arrays and
  functions that were difficult to fix. Natural number values are
  still available as scalars (where they are represented by integers with
  nonzero assumptions) via the `SymNat` type.

* Support for exporting What4 terms to Verilog syntax.

* Various documentation fixes and improvements.

* Test coverage improvements.

* Switch to use the `prettyprinter` package for user-facing output.

# 1.0 (July 2020)

* Initial Hackage release
