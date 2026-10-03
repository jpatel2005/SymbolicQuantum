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
balanced case the probability of reading the first `n` qubits as all zero is zero.

`Simon/` proves that any `y` with nonzero measurement probability satisfies `y · s = 0`.

`Shor/` has the classical reduction from factoring to order-finding, and the bound saying
at least half of the valid choices of `a` succeed.

`QFT/` has the quantum half of Shor. It proves the Fourier orthogonality sum, a lower bound
of `2M/π` on a geometric sum of `M` unit vectors whose phase is within `1/(2M)` of an
integer, and that the fibres of the oracle `x ↦ a^x mod N` are the residue classes mod the
period. `shors_algorithm_end_to_end` chains the three stages: the measurement probability,
recovery of the period as a continued-fraction convergent, and the factor of `N` that
follows. `shor_total_prob_ge_pi` gives the success probability `4/π²` when the period
divides `2 ^ n`.

## Scope

Gates are defined by their action on amplitudes. Unitarity and normalisation are not proved.

The QFT is specified by its action on amplitudes. It is not assembled from gates, and
neither are the oracles `Uf_DJA` and `Uf_Simon`.

`shor_total_prob_ge_pi` reaches `4/π²` when `r` divides `2 ^ n`. Otherwise only
`r - 2 ^ n % r` of the `r` fibres fit inside `2 ^ n`, which can be as few as one, and the
weaker `shor_total_prob_ge` applies instead.

`shors_algorithm_end_to_end` is stated for a fibre whose offset satisfies `2 ^ n % r ≤ x₀`.
`exists_offset`, `exists_good_measurement_bitString` and `shors_algorithm_concrete` supply
the witnesses and the progression count, so the caller is left with hypotheses about `N`,
`a` and the period.

No tracked file contains `sorry` or `axiom`.

## Building

```
lake exe cache get
lake build
```

## License

Apache-2.0. See [LICENSE](LICENSE).
