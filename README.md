# SymbolicQuantum

Formal verification of quantum algorithms in Lean 4, built on Mathlib.

Circuits are a deep embedding: `QGate` and `QCircuit` are inductive syntax, and `Qeval`
interprets them as functions on `QState n := BitString n → ℂ`. A state is a function on
bitstrings, not a vector of coefficients, so applying a gate rewrites a bitstring pointwise
and proofs come down to `funext` and case analysis.

## Contents

The core files hold the gate semantics, circuit equivalence, global-phase equivalence, and
the `qseq`, `qchain`, `qsimp` and `qunfold` tactics.

`DJA/` proves Deutsch, and Deutsch–Jozsa for the constant and balanced cases. In the
balanced case the probability of reading the first `n` qubits as all zero is zero. `Simon/` proves
that any `y` with nonzero measurement probability satisfies `y · s = 0`. `Shor/` has the
classical reduction from factoring to order-finding and the success-probability bound.

`QFT/` has the quantum half of Shor. The parts are the Fourier orthogonality sum, a lower
bound of `2M/π` on a geometric sum of `M` unit vectors whose phase is within `1/(2M)` of an
integer, and the fact that the fibres of the oracle `x ↦ a^x mod N` are the residue classes
mod the period. `shors_algorithm_end_to_end` puts the three stages together: the
measurement probability, recovery of the period as a continued-fraction convergent, and the
factor of `N` that follows.

## Scope

Gates are defined by their action on amplitudes. Unitarity and normalisation are not proved.

The QFT is specified by its action on amplitudes. It is not assembled from gates, and
neither are the oracles `Uf_DJA` and `Uf_Simon`.

`shors_algorithm_end_to_end` is stated for a fibre whose offset satisfies `2 ^ n % r ≤ x₀`.
That is what makes the progression fit inside `2 ^ n`, and `r - 2 ^ n % r` of the `r` offsets
satisfy it, so one always exists. `exists_offset` and `exists_good_measurement` construct
witnesses for the side conditions, and `shors_algorithm_concrete` computes the progression
count, so the only hypotheses left to the caller are about `N`, `a` and the period.

No tracked file contains `sorry` or `axiom`.

## Building

```
lake exe cache get
lake build
```

## License

Apache-2.0. See [LICENSE](LICENSE).
