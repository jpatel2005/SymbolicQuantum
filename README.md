# SymbolicQuantum

Formal verification of quantum algorithms in Lean 4, built on Mathlib.

Circuits are a deep embedding: `QGate` and `QCircuit` are inductive syntax, and `Qeval`
interprets them as functions on `QState n := BitString n → ℂ`. A state is a function on
bitstrings, not a vector of coefficients, so applying a gate rewrites a bitstring pointwise
and proofs come down to `funext` and case analysis.

## Contents

The core files hold the gate semantics, circuit equivalence, global-phase equivalence, and
the `qseq`, `qchain`, `qsimp` and `qunfold` tactics.

`DJA/` proves Deutsch, and Deutsch–Jozsa for the constant and balanced cases. `Simon/` proves
that any `y` with nonzero measurement probability satisfies `y · s = 0`. `Shor/` has the
classical reduction from factoring to order-finding and the success-probability bound.

## Scope

Gates are defined by their action on amplitudes. Unitarity and normalisation are not proved.

`Shor/` is classical only. There is no QFT and no quantum order-finding circuit.

No tracked file contains `sorry` or `axiom`.

## Building

```
lake exe cache get
lake build
```

## License

Apache-2.0. See [LICENSE](LICENSE).
