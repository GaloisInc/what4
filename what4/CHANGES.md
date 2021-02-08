# 1.1 (Febuary 2021)

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
  still avaliable as scalars (where they are repesented by integers with
  nonzero assumptions) via the `SymNat` type.

* Support for exporting What4 terms to Verilog syntax.

* Various documentation fixes and improvements.

* Test coverage improvements.

* Switch to use the `prettyprinter` package for user-facing output.

# 1.0 (July 2020)

* Initial Hackage release
