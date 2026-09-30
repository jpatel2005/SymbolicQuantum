# SymbolicQuantum

Formal verification of quantum algorithms in Lean 4, built on Mathlib.

Circuits are a deep embedding: `QGate`/`QCircuit` are inductive syntax, and `Qeval`
interprets them as functions on `QState n := BitString n → ℂ`. Representing a state as an
amplitude function rather than a vector makes gate application a pointwise rewrite of a
bitstring, so proofs reduce to `funext` and case analysis instead of linear algebra.

## Contents

- Core — gate semantics, circuit equivalence, global-phase equivalence, and the
  `qseq`/`qchain`/`qsimp`/`qunfold` tactics.
- `DJA/` — Deutsch, and Deutsch–Jozsa for the constant and balanced cases.
- `Simon/` — Simon's algorithm: any measurable `y` satisfies `y · s = 0`.
- `Shor/` — the classical reduction from factoring to order-finding, and the
  success-probability bound.

## Scope

Gates are defined by their action on amplitudes; unitarity and normalisation are not proved.

`Shor/` is classical only — there is no QFT and no quantum order-finding circuit.

No tracked file contains `sorry` or `axiom`.

## Building

```
lake exe cache get
lake build
```
