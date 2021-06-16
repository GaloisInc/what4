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
