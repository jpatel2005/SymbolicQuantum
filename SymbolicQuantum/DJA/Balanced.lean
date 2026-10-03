import SymbolicQuantum.DJA.DJA
import SymbolicQuantum.Simon.Simon

/-
  The balanced case as a measurement statement. `DJA_correctness_balanced` gives
  the amplitude at one basis state; what the algorithm needs is that reading the
  first n qubits as all zero has probability zero, which also covers the state
  with the ancilla set.
-/

lemma balanced_kickback_zero_gen {n : ℕ} (f : BitString n → Bool) (hf : isBalanced n f)
    (target : BitString (n + 1))
    (htarget : ∀ i : Fin (n + 1), (i : ℕ) < n → target i = Qubit.zero) :
    (〚H_post_DJA n〛 (ket_f_kickback f)) target = 0 := by
  unfold H_post_DJA
  rw [QRange_H_general_sum (n + 1) n (by omega)]
  have hdot : (fun i : Fin n => target ⟨i.val, by omega⟩) = fun _ => Qubit.zero := by
    funext i
    exact htarget ⟨i.val, by omega⟩ i.isLt
  rw [hdot]
  have hterm : ∀ x : BitString n,
      ket_f_kickback f (fun i : Fin (n + 1) => if hi : i.val < n then x ⟨i.val, hi⟩ else target i)
          * (-1 : ℂ) ^ (Qubit.toNat (dot_product x fun _ => Qubit.zero))
        = ((1 / Real.sqrt (2 ^ (n + 1)) : ℂ) *
            (match target ⟨n, Nat.lt_add_one n⟩ with
              | Qubit.zero => 1 | Qubit.one => -1))
          * (if f x then -1 else 1) := by
    intro x
    rw [dot_product_zero]
    unfold ket_f_kickback Qubit.toNat
    simp
    rfl
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  unfold isBalanced at hf
  rw [hf, mul_zero, mul_zero]

/-- **Deutsch-Jozsa, balanced case.** Measuring the first `n` qubits as all zero
    has probability zero. -/
theorem DJA_correctness_balanced_prob {n : ℕ} (f : BitString n → Bool) (hf : isBalanced n f) :
    prob_measure_y (〚deutsch_jozsa n f〛 (ket0n_M n)) (fun _ => Qubit.zero) = 0 := by
  unfold prob_measure_y
  apply Finset.sum_eq_zero
  intro z _
  rw [Complex.normSq_eq_zero]
  unfold deutsch_jozsa
  simp only [Qeval]
  rw [H_init_action_dja]
  have h_equiv : 〚H_post_DJA n〛 (〚oracle_block_DJA n f〛 (ketPn_M n))
      ≡ₚ 〚H_post_DJA n〛 (ket_f_kickback f) := Qeval_phase_eq _ _ _ (oracle_balanced_action f)
  rcases h_equiv with ⟨cc, hcc, hstate⟩
  rw [hstate]
  simp only [q_mul_apply]
  rw [balanced_kickback_zero_gen f hf, mul_zero]
  intro i hi
  simp [hi]
