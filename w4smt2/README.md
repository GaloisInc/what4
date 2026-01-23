# w4smt2

w4smt2 is a (bad) SMT solver built on What4's `ExprBuilder`. It takes SMT-Lib
files as input. It parses these files and builds up symbolic expressions using
the functions in `What4.Interface`. Upon encountering a `(check-sat)` command,
it inspects the predicate representing the query to see if the `ExprBuilder`
simplifications fully reduced it to a constant predicate. If so, it prints `sat`
or `unsat` appropriately. If not, it prints `unknown`.

w4smt2 is primarily intended as a tool for developers of What4. It is intended
to provide end-to-end tests for What4's abstract domains, rewrite rules, and
normalizing data structures (collectively, "simplifications"). Particular
use-cases include testing changes to What4's simplifications to see if they
maintain or improve:

- *correctness*, i.e., the output of w4smt2 more closely matches the output of
  an industrial-strength SMT solver
- *completeness*, i.e., the same or fewer SMT problems are marked as `unknown`
- *performance*, i.e., SMT problems can be processed in less time

As a developer-facing tool, our engineering standards for w4smt2 are lower than
for What4 itself. In particular, we are much more focused on its *extrinsic*
aspects (e.g., what SMT-Lib constructs it supports) than its *intrinsic* aspects
(e.g., the elegance and readability of its code). It also only needs to support
the lastest GHC version supported by What4, not all of them.

## w4smt2-bench

The w4smt2 package contains an executable called w4smt2-bench. It takes a
directory as input, recursively scans it for SMT-Lib files, and then runs w4smt2
in parallel over those files. It collects timing information and can optionally
verify results against Z3. See `cabal run exe:w4smt2-bench -- --help` for more
information.

## Test suite

w4smt2 has three main kinds of tests under `test/`:

- `golden/`: Hand-written SMT-Lib files that test the support for various
  SMT-Lib constructs, or test What4's simplifcations.
- `qf-bv/`: Unmodified tests from the `QF_BV` (quantifier-free theory of
  bitvectors) section of the [2025 SMT-LIB Benchmarks] (under the Creative
  Commons Attribution 4.0 International License).
- `ux/`: Test the User eXperience (i.e., log output) of w4smt

The results of w4smt2 on the `golden/` and `qf-bv/` tests are compared against
Z3 when available. w4smt2 is allowed to report `unknown` more often, but if it
reports `sat` or `unsat`, it must match Z3.

[2025 SMT-LIB Benchmarks]: https://zenodo.org/records/16740866
