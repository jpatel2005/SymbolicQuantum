import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import SymbolicQuantum.QuantumTactics
import SymbolicQuantum.DJA.Defs
import SymbolicQuantum.GlobalPhase
import SymbolicQuantum.QuantumLemmas

open QGate QCircuit

-- (Deutsch-Jozsa Algorithm)

lemma app_H_on_ket0_at (m n : ℕ) (h : n < m + 1) (ψ_prefix : QState (m+1))
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

lemma H_init_ket0n (n m : ℕ) (h : n ≤ m) :
  〚QRange_H (m+1) 0 n〛 (embed_arb (by omega) (ket0n n)) = embed_arb (by omega) (ketPn n) := by {
  induction n generalizing m with
  | zero =>
    qunfold [QRange_H, Qeval]
    rfl
  | succ n ih =>
    have hq : n < m + 1 := by omega
    rw [Qeval_QRange_succ_split]
    rw [ket0n_succ_split m n hq]
    simp only [Qeval]
    rw [QRange_H_distrib_disjoint m n (by omega)]
    {
      simp [hq, QRange_H, Qeval, Qeval_gate]
      rw [app_H_on_ket0_at m n hq]
      {
        rw [ketPn_succ_split m n hq]
        funext bs
        rw [ih]
        omega
      }
      {
        rw [ih]
        qunfold [π]
        omega
      }
    }
    {
      intros bs v i hi
      qunfold [π]
      congr
      funext k
      simp
      intro hnq
      subst hnq
      linarith
    }
}

lemma H_init_ket0n_M_gen (n m : ℕ) (h : n ≤ m) :
  (〚QRange_H (m+1) 0 n〛 (embed_arb (by simp [h]) (ket0n_M n))) = embed_arb (by simp [h]) (ketPn_M n) := by {
  have h_split_input : (embed_arb (by omega) (ket0n_M n) : QState (m+1)) =
    (fun bs => embed_arb (by omega) (ket0n n) bs * ketM (fun _ => bs ⟨n, by omega⟩)) := by qunfold [ket0n_M]
  have h_split_output : (embed_arb (by omega) (ketPn_M n) : QState (m+1)) =
    (fun bs => embed_arb (by omega) (ketPn n) bs * ketM (fun _ => bs ⟨n, by omega⟩)) := by qunfold [ketPn_M]
  rw [h_split_input, h_split_output]
  rw [QRange_H_distrib_disjoint m n (by omega)]
  { rw [H_init_ket0n n m h] }
  {
    intros bs v i hi
    unfold ketM
    simp
    rw [if_neg]
    intro hin
    subst hin
    linarith
  }
}

-- step 1 (initial hadamards)
lemma H_init_action_dja (n : ℕ) :
〚H_init_DJA n〛 (ket0n_M n) = ketPn_M n :=
H_init_ket0n_M_gen n n (Nat.le_refl n) -- generalized lemma with m = n

lemma H_init_eq_post (n : ℕ) : H_init_DJA n = H_post_DJA n := rfl

-- step 2 (final hadamards) - reverse direction
lemma H_post_action (n : ℕ) :
〚H_post_DJA n〛 (ketPn_M n) = ket0n_M n := by {
  rw [←H_init_eq_post n]
  rw [←H_init_action_dja n]
  unfold H_init_DJA
  exact QRange_H_involutive_general n n (Nat.le_succ n) (ket0n_M n)
}

-- step 3 (oracle action for constant functions)
lemma oracle_constant_kickback {n : ℕ} (f : BitString n → Bool) (hf : isConstant n f) :
〚oracle_block_DJA n f〛 (ketPn_M n) ≡ₚ ketPn_M n := by {
  unfold oracle_block_DJA
  unfold isConstant at hf
  cases hf with
  | inl ht =>
    simp [Qeval, Qeval_gate]
    unfold app_Uf_DJA app_X
    unfold ketPn_M embed_prefix embed_last ketPn ketM
    unfold tensor_product mask_left mask_right
    unfold GlobalPhaseEq
    simp [ht]
    split_ifs with hff
    {
      use -1
      simp
      funext bs
      simp
      cases (bs ⟨n, by simp⟩) <;> ring_nf
    }
    {
      use 1
      simp
      funext bs
      simp
    }
  | inr hf =>
    simp [Qeval, Qeval_gate]
    unfold app_Uf_DJA
    unfold ketPn_M embed_prefix embed_last ketPn ketM
    unfold tensor_product mask_left mask_right
    unfold GlobalPhaseEq
    use 1
    simp [hf]
    funext bs
    simp
}

theorem DJA_correctness_constant {n : ℕ} (f : BitString n → Bool) (hf: isConstant n f):
〚deutsch_jozsa n f〛 (ket0n_M n) ≡ₚ (ket0n_M n) := by {
  unfold deutsch_jozsa
  unfold Qeval Qeval
  rw [H_init_action_dja]
  rw [←H_post_action n]
  apply Qeval_phase_eq
  exact oracle_constant_kickback f hf
}

-- DJA balanced case

-- oracle action for balanced case (sending state to phase kickback state)
lemma oracle_balanced_action {n : ℕ} (f : BitString n → Bool) :
〚oracle_block_DJA n f〛 (ketPn_M n) ≡ₚ ket_f_kickback f := by {
  unfold oracle_block_DJA
  unfold ket_f_kickback
  simp [Qeval, Qeval_gate]
  unfold app_Uf_DJA app_X
  unfold ketPn_M embed_prefix embed_last ketPn ketM
  unfold tensor_product mask_left mask_right
  simp
  split_ifs with hc1
  {
    use 1
    simp
    funext bs
    simp
    cases bs ⟨n, Nat.lt_add_one n⟩
    {
      -- case last qubit is 0
      simp
      split_ifs with hq1 hq2 hq3
      {
        rw [pow_succ']
        norm_num
      }
      { contradiction }
      { contradiction }
      {
        rw [pow_succ']
        norm_num
      }
    }
    {
      simp
      split_ifs with hq1 hq2 hq3
      {
        rw [pow_succ']
        norm_num
      }
      { contradiction }
      { contradiction }
      {
        rw [pow_succ']
        norm_num
      }
    }
  }
  {
    use -1
    simp
    funext bs
    simp
    cases bs ⟨n, Nat.lt_add_one n⟩
    {
      simp
      split_ifs with hq1
      {
        rw [pow_succ']
        norm_num
      }
      { contradiction }
    }
    {
      simp
      split_ifs with hq1
      {
        rw [pow_succ']
        norm_num
      }
      { contradiction }
    }
  }
}

-- balanced correctness lemmas

-- generalized lemma
-- disjoint indices commute through QRange_H
lemma QRange_H_flip_invariant_gen (m k : ℕ) (n_idx : Fin (m + 1)) (h_disjoint : k ≤ n_idx)
  (ψ : QState (m + 1)) (b : BitString (m + 1)) (hb : b n_idx = Qubit.one) :
  let ψ_masked := fun bs ↦ if bs n_idx = Qubit.one then ψ bs else 0
  let ψ_shifted := fun bs ↦ ψ (Function.update bs n_idx Qubit.one)
  (〚QRange_H (m + 1) 0 k〛 ψ_masked) b = (〚QRange_H (m + 1) 0 k〛 ψ_shifted) (Function.update b n_idx Qubit.zero) := by {
  induction k generalizing m with
  | zero =>
    simp [QRange_H, Qeval, if_pos hb]
    congr
    funext i
    by_cases h : i = n_idx
    { rwa [h, Function.update_self] }
    { rw [Function.update_apply, if_neg h] }
  | succ k' ih =>
    have h_bound : k' < m + 1 := by omega
    have h_neq : (⟨k', h_bound⟩ : Fin (m + 1)) ≠ n_idx := by {
      apply ne_of_lt
      exact h_disjoint
    }
    simp [QRange_H, Qeval, h_bound, Qeval, Qeval_gate, app_H, Function.update_apply, if_neg h_neq]
    cases b ⟨k', h_bound⟩ <;>
    {
      simp
      congr 1
      all_goals {
        rw [ih]
        {
          congr
          funext i
          simp [Function.update]
          split_ifs with hc1 hc2 hc3 <;> try rfl
          try omega
        }
        omega
        split_ifs <;> omega
      }
    }
}

-- the sum of the amplitudes of the input state is equivalent to the amplitude of the |0...0⟩ state
lemma QRange_H_sum_property (n m : ℕ) (h : n ≤ m) (ψ : QState (m+1)) :
  (〚QRange_H (m+1) 0 n〛 ψ) (fun _ => Qubit.zero) =
  (1 / Real.sqrt (2^n)) * ∑ x : BitString n, ψ (embed_arb_zero x) := by {
  induction n generalizing ψ with
  | zero =>
    unfold QRange_H
    simp [Qeval]
    have h_unique_bs0 : (Finset.univ : Finset (BitString 0)) = {fun (i : Fin 0) => Fin.elim0 i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      constructor
      · simp
      · intro x hx
        funext i
        exact Fin.elim0 i
    rw [h_unique_bs0]
    rw [Finset.sum_singleton]
    congr
  | succ n ih =>
    have hq : n < m + 1 := by omega
    simp [QRange_H, Qeval, Qeval_gate, hq, app_H]
    rw [ih (by omega)]
    ring_nf
    simp
    have hq1 : ((↑√(2 ^ n)) : ℂ)⁻¹ = 1 / (↑√(2 ^ n)) := by norm_num
    rw [mul_comm ((↑√2)⁻¹ : ℂ) _]
    have sqrt2_ne : ((√2) : ℂ) ≠ 0 := by norm_num
    apply mul_left_cancel₀
    { exact inv_ne_zero sqrt2_ne }
    {
      ring_nf
      field_simp
      let ψ_one : QState (m + 1) := fun bs => ψ (fun i => if i = ⟨n, hq⟩ then Qubit.one else bs i)
      have h_gate_locality :
        (〚QRange_H (m + 1) 0 n〛 ψ fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero) =
        (〚QRange_H (m + 1) 0 n〛 ψ_one fun i ↦ Qubit.zero) := by {
        let g : BitString (m + 1) → ℂ := fun bs ↦ if bs ⟨n, hq⟩ = Qubit.one then 1 else 0
        have h_disjoint : ∀ (bs : BitString (m + 1)) (v : Qubit) (j : Fin (m + 1)),
          j < n → (g fun i ↦ if i = j then v else bs i) = g bs := by {
          intro bs v j hj
          dsimp [g]
          split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
          all_goals {
            exfalso
            cases hc1
            simp at hj
          }
        }
        have h_lhs_form : (〚QRange_H (m + 1) 0 n〛 ψ fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero)
          = (fun bs ↦ 〚QRange_H (m + 1) 0 n〛 ψ bs * g bs) fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero := by {
          dsimp [g]
          simp
        }
        rw [h_lhs_form]
        -- Apply the distribution lemma
        rw [←QRange_H_distrib_disjoint m n (by omega) ψ g h_disjoint]
        have g_at_input : g (fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero) = 1 := by simp [g]
        have factor_g : 〚QRange_H (m + 1) 0 n〛 (fun bs ↦ ψ bs * g bs) (fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero) =
          g (fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero) *
          〚QRange_H (m + 1) 0 n〛 ψ (fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero) := by simp [QRange_H_distrib_disjoint m n (by omega) ψ g h_disjoint, g_at_input]
        rw [factor_g, g_at_input]
        simp only [one_mul]
        have psi_to_psi_one : ∀ (bs : BitString (m + 1)),
            bs ⟨n, hq⟩ = Qubit.one →
            ψ bs = ψ_one (Function.update bs (⟨n, hq⟩ : Fin (m + 1)) Qubit.zero) := by {
          intros bs hbs
          simp only [ψ_one]
          congr 1
          funext i
          by_cases h : i = (⟨n, hq⟩ : Fin (m + 1))
          · subst h
            simpa
          · simp [Function.update_apply, if_neg h]
        }
        have update_gives_zeros : Function.update (fun i ↦ if i = (⟨n, hq⟩ : Fin (m + 1)) then Qubit.one else Qubit.zero)
                                                  (⟨n, hq⟩ : Fin (m + 1)) Qubit.zero =
                                  (fun i ↦ Qubit.zero) := by {
          ext i
          by_cases h : i = (⟨n, hq⟩ : Fin (m + 1))
          · subst h
            simp
          · simp [Function.update_apply, if_neg h]
        }
        have input_is_one : (fun i ↦ if i = (⟨n, hq⟩ : Fin (m + 1)) then Qubit.one else Qubit.zero) ⟨n, hq⟩ = Qubit.one := by simp
        rw [g_at_input, one_mul] at factor_g
        rw [←factor_g]
        have h_mask_eq : (fun bs ↦ ψ bs * g bs) = (fun bs ↦ if bs ⟨n, hq⟩ = Qubit.one then ψ bs else 0) := by {
          funext x
          dsimp [g]
          split_ifs <;> simp
        }
        rw [h_mask_eq]
        have hb_true : (fun i ↦ if i = ⟨n, hq⟩ then Qubit.one else Qubit.zero) (⟨n, hq⟩ : Fin (m+1)) = Qubit.one := by simp
        rw [QRange_H_flip_invariant_gen m n ⟨n, hq⟩ (by exact le_refl _) ψ _ hb_true]
        congr
        funext bs
        dsimp [ψ_one]
        congr
        funext i
        rw [Function.update_apply]
      }
      rw [h_gate_locality]
      rw [ih (by omega) ψ_one]
      field_simp [sqrt2_ne]
      let embed_0 (x : BitString n) : BitString (n+1) := fun i =>
        if h : i < n then x ⟨i, h⟩ else Qubit.zero
      let embed_1 (x : BitString n) : BitString (n+1) := fun i =>
        if h : i < n then x ⟨i, h⟩ else Qubit.one
      have h_sum_split :
        (∑ x : BitString n, ψ (embed_arb_zero (embed_0 x))) +
        (∑ x : BitString n, ψ (embed_arb_zero (embed_1 x))) =
      ∑ x : BitString (n + 1), ψ (embed_arb_zero x) := by {
        rw [sum_bitstring_split_last n (fun x => ψ (embed_arb_zero x))]
        rfl
      }
      have h_match_term1 : (∑ x : BitString n, ψ (embed_arb_zero x)) =
                           (∑ x : BitString n, ψ (embed_arb_zero (embed_0 x))) := by {
        unfold embed_arb_zero embed_0
        congr
        funext x
        congr
        funext i
        split_ifs with hc1 hc2 hc3
        { simp }
        { exfalso; omega }
        { rfl }
        { rfl }
      }
      have h_match_term2 : (∑ x : BitString n, ψ_one (embed_arb_zero x)) =
                           (∑ x : BitString n, ψ (embed_arb_zero (embed_1 x))) := by {
        congr; funext x; unfold ψ_one; congr; funext i
        split_ifs with hc1
        {
          unfold embed_arb_zero embed_1
          simp [hc1]
        }
        {
          unfold embed_arb_zero embed_1
          simp
          split_ifs with h1 h2 h3
          { rfl }
          { exfalso;omega }
          { exact hc1 (Fin.ext (by omega : i = n)) }
          { rfl}
        }
      }
      rw [h_match_term1, h_match_term2]
      exact h_sum_split
    }
}

-- the amplitude
lemma balanced_H_kickback_zero {n : ℕ} (f : BitString n → Bool) (hf : isBalanced n f) :
(〚H_post_DJA n〛 (ket_f_kickback f)) (fun _ => Qubit.zero) = 0 := by {
  unfold H_post_DJA
  rw [QRange_H_sum_property n n (by rfl)]
  unfold ket_f_kickback embed_arb_zero
  unfold isBalanced at hf
  simp [Finset.mul_sum]
  have ht2 : (((↑√(2 ^ n) : ℂ))⁻¹ * (↑√(2 ^ (n + 1)))⁻¹) = ((↑√(2 ^ (2*n+1)))⁻¹) := by {
    have : ((2 ^ (2 * n + 1)) : ℝ) = (2 ^ n) * (2 ^ (n + 1)) := by qsimp
    qsimp[this]
  }
  have hq : (∑ (x : BitString n), if (f fun i ↦ x i) = true then -(((√(2 ^ (2 * n + 1)))) : ℂ)⁻¹ else (((√(2 ^ (2 * n + 1)))) : ℂ)⁻¹) =
        (((√(2 ^ (2 * n + 1)))) : ℂ)⁻¹ * (∑ x, if f x = true then (-1 : ℂ) else 1) := by {
    simp only [Finset.mul_sum]
    congr 1
    funext k
    split_ifs <;> simp
  }
  simp only [ht2,hq,hf,mul_zero]
}

theorem DJA_correctness_balanced {n : ℕ} (f : BitString n → Bool) (hf: isBalanced n f) :
Complex.normSq (〚deutsch_jozsa n f〛 (ket0n_M n) (fun _ => Qubit.zero)) = 0 := by {
  unfold deutsch_jozsa
  unfold Qeval Qeval
  rw [H_init_action_dja]
  have h_equiv : 〚H_post_DJA n〛 (〚oracle_block_DJA n f〛 (ketPn_M n)) ≡ₚ 〚H_post_DJA n〛 (ket_f_kickback f) := by {
    apply Qeval_phase_eq
    exact oracle_balanced_action f
  }
  rcases h_equiv with ⟨c, hc_nonzero, h_state_eq⟩
  simp [h_state_eq, hc_nonzero]
  exact balanced_H_kickback_zero f hf
}
