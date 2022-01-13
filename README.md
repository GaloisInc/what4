What4 is a library for representing symbolic terms and communicating with
satisfiability and SMT solvers (e.g. Yices and Z3).

It was originally a part of the [Crucible](https://github.com/GaloisInc/crucible)
project, but has found use cases that are independent of its original
purpose as the representation language for the Crucible symbolic
simulator, and has thus been split out into a separate repository.

For an overview of What4 and how to use it, please see the
package-level [README](what4/README.md).

This material is based upon work supported by the Defense Advanced
Research Projects Agency (DARPA) under Contract No. HR0011-19-C-0070.
The views, opinions, and/or findings expressed are those of the
author(s) and should not be interpreted as representing the official
views or policies of the Department of Defense or the U.S. Government.


# Solver Compatibility

| Feature                               | ABC | Boolector   | CVC4      | Dreal | STP         | Yices    | Z3              |
|---------------------------------------|-----|-------------|-----------|-------|-------------|----------|-----------------|
| Supported                             | yes | >= 3.2.0, ? | >= 1.8, ? | yes   | >= 2.3.3, ? | 2.6.x, ? | 4.8.8 -- 4.8.14 |
| goal timeouts                         | ?   | yes         | yes       | ?     | yes         | yes      | ! 4.8.12        |
| strings with unicode and escape codes | ?   | ?           | >= 1.8    | ?     | ?           | ?        | >= 4.8.11       |
