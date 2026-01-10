import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumTactics

open QGate QCircuit

/-

Theorem [CNOT_rev]:

[LHS]
Qubit 0: ─────── H ───────── ● ──────────── H ───────
                             |
Qubit 1: ─────── H ───────── ⊕ ──────────── H ───────

[RHS]
Qubit 0: ─────── ⊕ ───────
                 |
Qubit 1: ─────── ● ───────
-/

theorem CNOT_rev {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
(app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H i) ≫ app (H j)) ≡
(app (CNOT j i)) := by {
  -- proof outline:
  -- commute app (H i) and app (H j)
  -- rewrite middle: [app (H j) ≫ app (CNOT i j) ≫ app (H j)] as CZ
  -- this gives app (H i) ≫ app (CZ i j) ≫ app (H i)
  -- rewrite middle: [app (CZ i j)] as [app (CZ j i)]
  -- this gives app (H i) ≫ app (CZ j i) ≫ app (H i)
  -- rewrite entire expression as [app (CNOT j i)]
  -- ▪
  have s1 :
  (app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H i) ≫ app (H j)) ≡
  (app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i))
  := by {
    qseq (H_comm_H hij)
  }
  have s2 :
  (app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i)) ≡
  (app (H i) ≫ app (CZ i j) ≫ app (H i)) := by {
    -- app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i) ≡ app (H i) ≫ app (CZ i j) ≫ app (H i)
    qseq (H_CNOT_H_eq_CZ hij)
  }
  -- app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i) ≡ app (CNOT j i)
  -- app (H i) ≫ app (CZ i j) ≫ app (H i) ≡ app (CNOT j i)
  have s3 :
  (app (H i) ≫ app (CZ i j) ≫ app (H i)) ≡
  (app (H i) ≫ app (CZ j i) ≫ app (H i)) := by {
    qseq (CZ_comm_CZ hij)
  }
  -- app (H i) ≫ app (CZ j i) ≫ app (H i) ≡ app (CNOT j i)
  have s4 :
  (app (H i) ≫ app (CZ j i) ≫ app (H i)) ≡
  (app (CNOT j i)) := by {
    qseq (H_CZ_H_eq_CNOT)
    exact hij.symm
  }
  -- apply steps as a transitivity chain
  qchain s1, s2, s3, s4
}
