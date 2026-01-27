import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import SymbolicQuantum.QuantumTactics
import SymbolicQuantum.Simon.Defs
import SymbolicQuantum.GlobalPhase
import SymbolicQuantum.QuantumLemmas

-- (Simon's Algorithm)

lemma app_H_on_ket0_at (n k : ℕ) (h : n < k) (ψ_prefix : QState k)
  (h_disjoint : ∀ bs, ψ_prefix (Function.update bs ⟨n, h⟩ Qubit.one) = ψ_prefix bs) :
  app_H (fun bs => ψ_prefix bs * ket0 (fun _ => bs ⟨n, h⟩)) ⟨n, h⟩ =
  (fun bs => ψ_prefix bs * ketP (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  have h_psi_0 : ψ_prefix (Function.update bs ⟨n, h⟩ Qubit.zero) = ψ_prefix bs := by {
    rw [←h_disjoint]
    simp
    rw [h_disjoint]
  }
  simp only [app_H, ket0, ketP, basis_state]
  have h_neq : (fun (_ : Fin 1) ↦ Qubit.one) ≠ (fun _ ↦ Qubit.zero) := by {
    intro _; contradiction
  }
  simp [h_neq, mul_zero, add_zero, sub_zero]
  cases bs ⟨n, h⟩ <;>
  {
    simp [←h_psi_0]
    congr
    funext k
    simp [Function.update_apply]
  }
}

lemma ketPn_succ_split_gen (n k : ℕ) (h : n < k) :
  embed_arb (by omega) (ketPn (n + 1)) =
  (fun bs => embed_arb (by omega) (ketPn n) bs * ketP (fun _ => bs ⟨n, h⟩)) := by {
  funext bs
  qunfold [π]
  cases bs ⟨n,h⟩ <;> qsimp [mul_comm]
}

lemma H_init_ket0n_0m (k n : ℕ) (hkn : k > n) :
〚QRange_H k 0 n〛 (embed_arb (by omega) (ket0n n)) = embed_arb (by omega) (ketPn n):= by {
  induction n generalizing k with
  | zero =>
    qunfold [QRange_H, Qeval]
    rfl
  | succ n ih =>
    have hk : n < k := by omega
    rw [Qeval_QRange_succ_split, zero_add]
    rw [ket0n_succ_split_gen n k (by omega)]
    simp only [Qeval]
    rw [QRange_H_distrib_disjoint_gen n k (by omega)]
    {
      simp [QRange_H, Qeval, hk, Qeval_gate]
      rw [app_H_on_ket0_at n k (by omega)]
      {
        rw [ketPn_succ_split_gen n k (by omega)]
        funext bs
        rw [ih]
        exact hk
      }
      {
        rw [ih]
        qunfold [π]
        exact hk
      }
    }
    {
      intros bs v i hi
      qunfold [π]
      congr
      funext l
      simp
      intro hnq
      subst hnq
      linarith
    }
}

lemma H_init_simon_gen (n m : ℕ) (hmn : m > 0 ∧ n > 0):
〚QRange_H (n + m) 0 n〛 (ket0n_0m n m) = ketPn_0m n m := by {
  have h_split_input : ket0n_0m n m =
    (fun bs => (embed_arb (by omega) (ket0n n)) bs * (embed_suffix (ket0n m)) bs) := by qunfold [π]
  have h_split_output : ketPn_0m n m =
    (fun bs => (embed_arb (by omega) (ketPn n)) bs * (embed_suffix (ket0n m)) bs) := by qunfold [π]
  rw [h_split_input, h_split_output]
  rw [QRange_H_distrib_disjoint_gen n (n + m) (by omega)]
  { rw [H_init_ket0n_0m (n+m) n (by omega)] }
  {
    intros bs v i hi
    qunfold [π]
    congr
    funext k
    simp
    intro eq
    exfalso
    subst eq
    simp at hi
  }
}

lemma H_init_action_simon (n m : ℕ) (h_mpos : m > 0) (h_npos : n > 0) : 〚H_init_simon n m〛 (ket0n_0m n m) = ketPn_0m n m :=
H_init_simon_gen n m (by omega)

theorem simons_correctness {n m : ℕ} (f : BitString n → BitString m) (s : BitString n) (hf : simons_promise f s)
(hmn : m > 0 ∧ n > 0) :
∀ y : BitString n, prob_measure_y (〚simon n m f〛 (ket0n_0m n m)) y > 0 → dot_product y s = Qubit.zero := by {
  unfold simon
  simp [Qeval]
  rw [H_init_action_simon n m hmn.1 hmn.2]
  sorry
}
