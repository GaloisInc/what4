# 1.2 (June 2021)

This is primarily a bugfix release, but also adds support
for GHC 9.x

* Tweaks to the `SolverEvent` data type to remove partial
fields.

* Fix issue #126.  The shift operations of `What4.SWord` were
not correctly handling cases where the shift amount has more
bits than the word to be shifted.

* Fix issue #121. The ordering of inputs in generated Verilog
files is now more predictable.

* Fix issue #113.  The `bvSliceLE` and `bvSliceBE` functions of
`What4.SWord` did not properly handle size 0 bit-vectors and
requests for 0 length slices.  They now correctly fail for slice
lengths longer than 0 on 0-length vectors, and correctly
allow 0 length slices regardless of the length of the input.

* Fix issue #103. Some of the string operations would give incorrect
results when string offsets are out-of-bounds.  The SMTLib 2.6 standard
specifies precise results for these cases, which we now implement.

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
