# Who2

Who2 provides a configurable alternative to What4's `ExprBuilder` that uses only
approximately linear time by default. See the Haddocks in the following modules
for more information:

- `Who2.Builder`
- `Who2.Config`
- `Who2.Expr.App`

## Status

Only logical and bitvector operations are currently supported (`QF_BV`).
Unsupported operations throw a dedicated `Unsupported` exception.

## Future work

- Benchmark uses of Who2 in downstream consumers (e.g., Crucible, SAW)
- Support the remaining `Is{,Sym}ExprBuilder` methods
- What4-like interface to solvers
