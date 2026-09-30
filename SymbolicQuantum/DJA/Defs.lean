import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumDefs

open QGate QCircuit

-- (Deutsch-Jozsa Algorithm Definitions)

def H_init_DJA (n : ℕ) : QCircuit (n+1) :=
  QRange_H (n+1) 0 n

def H_post_DJA (n : ℕ) : QCircuit (n+1) :=
  QRange_H (n+1) 0 n

def oracle_block_DJA (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  app (Uf_DJA f)

def deutsch_jozsa (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  H_init_DJA n ≫
  oracle_block_DJA n f ≫
  H_post_DJA n

def isConstant (n : ℕ) (f : BitString n → Bool) :=
  (∀ x, f x = true) ∨ (∀ x, f x = false)

def isBalanced (n : ℕ) (f : BitString n → Bool) : Prop :=
  Finset.sum Finset.univ (fun x => if f x then (-1 : ℂ) else 1) = 0

-- isBalanced agrees with the combinatorial definition
lemma isBalanced_iff (n : ℕ) (f : BitString n → Bool) :
  isBalanced n f ↔
  (Finset.univ.filter (fun x => f x = true)).card
    = (Finset.univ.filter (fun x => f x = false)).card := by {
  unfold isBalanced
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp [neg_add_eq_zero]
}

-- phase kickback state
noncomputable def ket_f_kickback {n : ℕ} (f : BitString n → Bool) : QState (n + 1) :=
  fun bs =>
  (1 / Real.sqrt (2^(n+1)) : ℂ) * (if f (fun i => bs ⟨i, by omega⟩) then -1 else 1) *
  (match bs ⟨n, Nat.lt_add_one n⟩ with
    | Qubit.zero => 1
    | Qubit.one  => -1
  )
