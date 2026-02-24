import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import SymbolicQuantum.QuantumTactics
import SymbolicQuantum.Simon.Defs
import SymbolicQuantum.GlobalPhase
import SymbolicQuantum.QuantumLemmas

-- (Simon's Algorithm)

-- applying a single Haddamard to the nth qubit |0⟩ only changes the nth qubit to |+⟩
lemma app_H_on_ket0_at_gen (n k : ℕ) (h : n < k) (ψ_prefix : QState k)
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

-- applying Haddamard gates to the first n qubits in the |0⟩ state transforms those to the |+⟩ state
lemma H_init_ket0n_0m (k n : ℕ) (hkn : k > n) :
〚QRange_H k 0 n〛 (embed_arb (by omega) (ket0n n)) = embed_arb (by omega) (ketPn n) := by {
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
      rw [app_H_on_ket0_at_gen n k (by omega)]
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

-- first step for Simon's
-- first n qubits are in |+⟩ state, last m qubits are in |0⟩ state
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

-- applying general lemma
lemma H_init_action_simon (n m : ℕ) (h_mpos : m > 0) (h_npos : n > 0) : 〚H_init_simon n m〛 (ket0n_0m n m) = ketPn_0m n m :=
H_init_simon_gen n m (by omega)

-- oracle block for Simon's
-- maps |x⟩|y⟩ to |x⟩|y ⊕ f(x)⟩
lemma ket_simon_equiv (n m : ℕ) (h_mpos : m > 0) (f : BitString n → BitString m) :
  app_Uf_Simon (fun bs ↦ if (fun (i : Fin m) ↦ bs ⟨n + i, by omega⟩) = fun _ ↦ Qubit.zero then ((√(2 ^ n) : ℂ))⁻¹ else 0) f = ket_simon n m f := by {
  funext bs
  qsimp [ket_simon, app_Uf_Simon]
  congr 1
  apply propext
  constructor
  {
    intro hx_zero
    funext i
    have h_bit := congr_fun hx_zero i
    simp at h_bit
    cases hfi : f (fun k ↦ bs ⟨k, by omega⟩) i
    {
      simp [hfi] at h_bit
      assumption
    }
    {
      simp [hfi] at h_bit
      split at h_bit <;> simp_all
    }
  }
  {
    intro h_eq
    apply congr_fun at h_eq
    funext i
    cases hfk : f (fun k ↦ bs ⟨k, by omega⟩) i <;> simp [h_eq, hfk]
  }
}

-- applying main oracle lemma
lemma oracle_action_simon (n m : ℕ) (h_mpos : m > 0) (f : BitString n → BitString m) :
〚oracle_block_simon n m f〛 (ketPn_0m n m) = ket_simon n m f := by {
  qunfold [oracle_block_simon]
  simp [Qeval, Qeval_gate]
  exact ket_simon_equiv n m h_mpos f
}

-- final step for Simon's
-- applying the final layer of Haddamard gates
lemma QRange_H_general_sum (N n : ℕ) (hn : n ≤ N) (ψ : QState N) (target : BitString N) :
〚QRange_H N 0 n〛 ψ target =
(↑√(2 ^ n))⁻¹ * ∑ x : BitString n, ψ (fun i => if hi : i.val < n then x ⟨i.val, hi⟩ else target i) * (-1 : ℂ)^(Qubit.toNat (dot_product x (fun i => target ⟨i.val, by omega⟩))) := by {
  induction n generalizing target with
  | zero => qunfold [QRange_H, Qeval, dot_product, BitString, Qubit.toNat]
  | succ k ih =>
    have hk : k ≤ N := by omega
    have hk_lt : k < N := by omega
    unfold QRange_H
    qunfold [Qeval]
    simp only [hk_lt, dif_pos, Qeval, Qeval_gate]
    unfold app_H
    dsimp
    have h_eval_zero := ih hk (fun i => if i = ⟨k, hk_lt⟩ then Qubit.zero else target i)
    have h_eval_one  := ih hk (fun i => if i = ⟨k, hk_lt⟩ then Qubit.one else target i)
    rw [sum_bitstring_split_last]
    -- 1. match on target's kth bit
    split
    · -- ==========================================
      -- Case 1: target k = Qubit.zero
      -- ==========================================
      rename_i h_targ_zero
      simp only [h_eval_zero, h_eval_one]
      rw [← mul_add]
      have h_rearrange : ∀ (A B C : ℂ), (A * B) * C = (A * C) * B := by intros; ring
      rw [h_rearrange]
      -- 2. algebra
      have h_pow : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := by ring
      have h_sqrt : Real.sqrt ((2 : ℝ) ^ (k + 1)) = Real.sqrt (2 ^ k) * Real.sqrt 2 := by
        rw [pow_succ, ←Real.sqrt_mul (by simp)]
      have h_cast : (↑(Real.sqrt ((2 : ℝ) ^ (k + 1))) : ℂ) = ↑(Real.sqrt (2 ^ k)) * ↑(Real.sqrt 2) := by
        rw [h_sqrt]; push_cast; rfl
      have h_scalar_combine : (↑√(2 ^ k) : ℂ)⁻¹ * (1 / ↑√2) = (↑√(2 ^ (k + 1)))⁻¹ := by
        rw [one_div, ← mul_inv]
        rw [h_cast]
      rw [h_scalar_combine]

      -- 3. isolate the sums
      congr 2
      ·
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        ·
          congr 1
          funext i
          split_ifs with h1 h2 h3 h4 h5 <;> (try rfl)
          {
            have : (⟨↑i, h2⟩ : Fin (k + 1)) = Fin.castSucc ⟨↑i, h1⟩ := by
              simp [Fin.castSucc]
            rw [this, Fin.snoc_castSucc]
          }
          { omega }
          {
            have : (⟨↑i, h4⟩ : Fin (k + 1)) = Fin.last k := by
              simp [Fin.ext_iff, Fin.last]
              omega
            rw [this, Fin.snoc_last]
          }
          { rw [h3, h_targ_zero] }
          {
            exfalso
            apply h3
            ext
            simp [Fin.ext_iff] at h3
            omega
          }
        ·
          congr 2
          have h_lhs_dot_arg : (fun (j : Fin k) ↦ if (⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩ then Qubit.zero else target ⟨↑j, by omega⟩) = fun (j : Fin k) ↦ target ⟨↑j, by omega⟩ := by
            funext j
            have h_neq : ¬((⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩) := by
              intro h_eq
              injection h_eq with h_eq_val
              have hj : ↑j < k := j.isLt
              omega
            simp [h_neq]
          rw [h_lhs_dot_arg]
          simp [dot_product_snoc, h_targ_zero]
          cases (dot_product x fun i ↦ target ⟨↑i, by omega⟩) <;> rfl
      · -- ==========================================
        -- 2. Align the Qubit.one Sums
        -- ==========================================
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        ·
          congr 1
          funext i
          split_ifs with h1 h2 h3 h4 h5 <;> try rfl
          {
            have : (⟨↑i, h2⟩ : Fin (k + 1)) = Fin.castSucc ⟨↑i, h1⟩ := by
              simp [Fin.castSucc]
            rw [this, Fin.snoc_castSucc]
          }
          { omega }
          {
            have : (⟨↑i, h4⟩ : Fin (k + 1)) = Fin.last k := by
              simp [Fin.ext_iff, Fin.last]
              omega
            rw [this, Fin.snoc_last]
          }
          {
            exfalso
            apply h4
            rw [h3]
            simp
          }
          {
            exfalso
            apply h3
            ext
            simp [Fin.ext_iff] at h3
            omega
          }

        ·
          congr 2
          have h_lhs_dot_arg : (fun (j : Fin k) ↦ if (⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩ then Qubit.one else target ⟨↑j, by omega⟩) = fun (j : Fin k) ↦ target ⟨↑j, by omega⟩ := by
            funext j
            have h_neq : ¬((⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩) := by
              intro h_eq; injection h_eq with h_eq_val; have hj : ↑j < k := j.isLt; omega
            simp [h_neq]
          rw [h_lhs_dot_arg]
          simp [dot_product_snoc, h_targ_zero]
          cases (dot_product x fun i ↦ target ⟨↑i, by omega⟩) <;> rfl

    · -- ==========================================
      -- Case 2: target k = Qubit.one
      -- ==========================================
      rename_i h_targ_one
      simp only [h_eval_zero, h_eval_one]
      rw [← mul_sub]
      have h_rearrange : ∀ (A B C : ℂ), (A * B) * C = (A * C) * B := by intros; ring
      rw [h_rearrange]
      have h_pow : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := by ring
      have h_sqrt : Real.sqrt ((2 : ℝ) ^ (k + 1)) = Real.sqrt (2 ^ k) * Real.sqrt 2 := by
        rw [pow_succ, ←Real.sqrt_mul (by simp)]
      have h_cast : (↑(Real.sqrt ((2 : ℝ) ^ (k + 1))) : ℂ) = ↑(Real.sqrt (2 ^ k)) * ↑(Real.sqrt 2) := by
        rw [h_sqrt]; push_cast; rfl
      have h_scalar_combine : (↑√(2 ^ k) : ℂ)⁻¹ * (1 / ↑√2) = (↑√(2 ^ (k + 1)))⁻¹ := by
        rw [one_div, ← mul_inv]
        rw [h_cast]
      rw [h_scalar_combine]
      rw [sub_eq_add_neg]
      rw [← Finset.sum_neg_distrib]
      congr 2
      · -- ==========================================
        -- 1. Align the Qubit.zero Sums
        -- ==========================================
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        ·
          congr 1
          funext i
          split_ifs with h1 h2 h3 h4 h5 <;> try rfl
          { have : (⟨↑i, h2⟩ : Fin (k + 1)) = Fin.castSucc ⟨↑i, h1⟩ := by simp [Fin.castSucc]
            rw [this, Fin.snoc_castSucc] }
          { omega }
          { have : (⟨↑i, h4⟩ : Fin (k + 1)) = Fin.last k := by simp [Fin.ext_iff, Fin.last]; omega
            rw [this, Fin.snoc_last] }
          { exfalso; apply h4; rw [h3]; simp }
          { exfalso; apply h3; ext; simp [Fin.ext_iff] at h3; omega }

        ·
          congr 2
          have h_lhs_dot_arg : (fun (j : Fin k) ↦ if (⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩ then Qubit.zero else target ⟨↑j, by omega⟩) = fun (j : Fin k) ↦ target ⟨↑j, by omega⟩ := by
            funext j
            have h_neq : ¬((⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩) := by
              intro h_eq; injection h_eq with h_eq_val; have hj : ↑j < k := j.isLt; omega
            simp [h_neq]
          rw [h_lhs_dot_arg]
          simp [dot_product_snoc, h_targ_one]
          cases (dot_product x fun i ↦ target ⟨↑i, by omega⟩) <;> rfl

      · -- ==========================================
        -- 2. Align the Qubit.one Sums
        -- ==========================================
        apply Finset.sum_congr rfl
        intro x _
        have h_neg_shift : ∀ (S P : ℂ), -(S * P) = S * -P := by intros; ring
        rw [h_neg_shift]
        congr 1
        ·
          congr 1
          funext i
          split_ifs with h1 h2 h3 h4 h5 <;> try rfl
          { have : (⟨↑i, h2⟩ : Fin (k + 1)) = Fin.castSucc ⟨↑i, h1⟩ := by simp [Fin.castSucc]
            rw [this, Fin.snoc_castSucc] }
          { omega }
          { have : (⟨↑i, h4⟩ : Fin (k + 1)) = Fin.last k := by simp [Fin.ext_iff, Fin.last]; omega
            rw [this, Fin.snoc_last] }
          { exfalso; apply h4; rw [h3]; simp }
          { exfalso; apply h3; ext; simp [Fin.ext_iff] at h3; omega }

        ·
          have h_lhs_dot_arg : (fun (j : Fin k) ↦ if (⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩ then Qubit.one else target ⟨↑j, by omega⟩) = fun (j : Fin k) ↦ target ⟨↑j, by omega⟩ := by
            funext j
            have h_neq : ¬((⟨↑j, by omega⟩ : Fin N) = ⟨k, hk_lt⟩) := by
              intro h_eq; injection h_eq with h_eq_val; have hj : ↑j < k := j.isLt; omega
            simp [h_neq]
          rw [h_lhs_dot_arg]
          simp [dot_product_snoc, h_targ_one, Qubit.toNat, bxor, band]
          cases (dot_product x fun i ↦ target ⟨↑i, by omega⟩) <;> simp
}

-- computes the amplitude of measuring |y⟩|z⟩ after applying the final layer of Haddamard gates in Simon's algorithm
lemma simon_amplitude_sum (n m : ℕ) (f : BitString n → BitString m) (y : BitString n) (z : BitString m) :
  (〚QRange_H (n + m) 0 n〛 (ket_simon n m f)) (combine y z) =
  (1 / (2^n : ℂ)) * ∑ x : {x // f x = z}, (-1 : ℂ)^(Qubit.toNat (dot_product x.val y)) := by {
  have h_fixed := QRange_H_general_sum (n + m) n (by omega) (ket_simon n m f) (combine y z)
  have h_simplify_combine :
  (fun i : Fin n => (combine y z) ⟨i.val, by omega⟩) = y ∧
  (∀ x, (fun i : Fin (n + m) => if hi : i.val < n then x ⟨i.val, hi⟩ else combine y z i) = combine x z) := by {
    constructor
    {
      funext i
      unfold combine
      simp
    }
    {
      intro x
      unfold combine
      funext i
      congr
      funext hin
      simp [hin]
    }
  }
  rw [h_simplify_combine.1] at h_fixed
  simp only [h_simplify_combine.2] at h_fixed
  rw [h_fixed]
  rw [Finset.mul_sum]
  have rhs_subtype_to_if :
    ((1 / (2^n : ℂ)) * ∑ x : {x // f x = z}, (-1 : ℂ)^(Qubit.toNat (dot_product x.val y))) =
    ∑ x : BitString n, if f x = z then (1 / (2^n : ℂ)) * (-1 : ℂ)^(Qubit.toNat (dot_product x y)) else 0 := by {
    rw [Finset.mul_sum]
    symm
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun x _ ↦ ⟨x, by simp_all⟩)
    {
      intros a ha
      exact Finset.mem_univ _
    }
    {
      intros a ha a₂ ha₂ a_1
      simp_all
    }
    {
      -- inj.
      intro b a
      obtain ⟨val, property⟩ := b
      subst property
      simp_all
    }
    {
     -- surj.
      intros b _
      simp_all
    }
  }
  rw [rhs_subtype_to_if]
  apply Finset.sum_congr rfl
  intro x _
  unfold ket_simon
  have extract_combine :
  (fun (i : Fin n) ↦ combine x z ⟨i.val, by omega⟩) = x ∧
  (fun (i : Fin m) ↦ combine x z ⟨n + i.val, by omega⟩) = z := by {
    constructor <;>
    {
      unfold combine
      funext i
      simp
    }
  }
  simp
  split_ifs with hc1 hc2 hc3
  {
    field_simp
    norm_cast
    norm_num
  }
  {
    exfalso
    rw [extract_combine.1, extract_combine.2] at hc1
    exact hc2 hc1.symm
  }
  {
    exfalso
    rw [extract_combine.1, extract_combine.2] at hc1
    exact hc1 hc3.symm
  }
  { rfl }
}

-- the amplitude for measuring |y⟩|z⟩ can be expressed as a sum over the preimages of z under f,
-- with phases determined by the dot product of y with those preimages
lemma simon_sum_grouping (n m : ℕ) (f : BitString n → BitString m) (s : BitString n)
  (hf : simons_promise f s) (y : BitString n) (z : BitString m)
  (x₀ : BitString n) (hx₀ : f x₀ = z) (hs_nz : s ≠ (fun _ => Qubit.zero)) :
  (∑ x : {x // f x = z}, (-1 : ℂ)^(Qubit.toNat (dot_product x.1 y))) =
  (-1 : ℂ)^(Qubit.toNat (dot_product x₀ y)) + (-1 : ℂ)^(Qubit.toNat (dot_product (bs_xor x₀ s) y)) := by {
  let x₁ := bs_xor x₀ s
  have hx₁ : f x₁ = z := by {
    rw [←hx₀, hf x₁ x₀]
    right
    intro _
    rfl
  }
  let el₀ : {x // f x = z} := ⟨x₀, hx₀⟩
  let el₁ : {x // f x = z} := ⟨x₁, hx₁⟩
  have h_distinct : el₀ ≠ el₁ := by {
    intro h_eq
    have h_val_eq : x₀ = x₁ := (Subtype.ext_iff.mp h_eq)
    have h_s_zero : s = (fun _ => Qubit.zero) := by {
      rw [← bs_xor_self x₀]
      nth_rw 1 [h_val_eq]
      subst x₁
      rw [bs_xor_comm x₀ s, bs_xor_distrib, bs_xor_self]
      qunfold [bs_xor, bxor]
      funext i
      cases (s i) <;> simp
    }
    contradiction
  }
  have h_univ_eq : (Finset.univ : Finset {x // f x = z}) = {el₀, el₁} := by {
    ext a
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    let val := a.val
    have h_val_z : f val = z := a.property
    rw [← hx₀] at h_val_z
    specialize hf val x₀
    rw [hf] at h_val_z
    cases h_val_z with
    | inl h_is_x0 =>
      left
      apply Subtype.ext
      exact h_is_x0
    | inr h_is_x1 =>
      right
      apply Subtype.ext
      funext i
      simp_all [el₀, el₁, x₁, val]
      rfl
  }
  rw [h_univ_eq]
  rw [Finset.sum_pair h_distinct]
}

-- if the sum of the amplitudes for measuring |y⟩|z⟩ is nonzero,
-- then the phases contributed by the two preimages of z under f must interfere constructively,
-- which impies that the dot product of y with s is zero
lemma phase_interference_zero {n : ℕ} (y s x₀ : BitString n) :
  ((-1 : ℂ)^(Qubit.toNat (dot_product x₀ y)) + (-1 : ℂ)^(Qubit.toNat (dot_product (bs_xor x₀ s) y))) ≠ 0 →
  dot_product y s = Qubit.zero := by {
  intro h_sum_nz
  rw [dot_product_distrib] at h_sum_nz
  rw [dot_product_comm s y] at h_sum_nz
  by_contra h_not_zero
  have h_is_one : dot_product y s = Qubit.one := by {
    cases hd_ys : (dot_product y s) using Qubit.casesOn
    · contradiction
    · rfl
  }
  rw [h_is_one] at h_sum_nz
  let a := dot_product x₀ y
  have h_cancel : (-1 : ℂ)^(Qubit.toNat a) + (-1 : ℂ)^(Qubit.toNat (bxor a Qubit.one)) = 0 := by {
    cases a using Qubit.casesOn <;> qunfold [bxor, Qubit.toNat]
  }
  rw [h_cancel] at h_sum_nz
  contradiction
}

-- if the probability of measuring |y⟩|z⟩ is nonzero, then the dot product of y with s must be zero
lemma simons_prob_measure_y {n m : ℕ} (f : BitString n → BitString m) (s : BitString n) (hf : simons_promise f s) :
∀ (y : BitString n), 0 < prob_measure_y (〚H_post_simon n m〛 (ket_simon n m f)) y → dot_product y s = Qubit.zero := by {
  unfold prob_measure_y
  intro y h_prob_pos
  have ⟨z, _, hz_pos⟩ : ∃ z, z ∈ (Finset.univ : Finset (BitString m)) ∧
    Complex.normSq ((〚H_post_simon n m〛 (ket_simon n m f)) (combine y z)) > 0 := by {
    apply Finset.exists_lt_of_sum_lt (f := fun _ => 0)
    simp only [Finset.sum_const_zero]
    exact h_prob_pos
  }
  rw [gt_iff_lt, Complex.normSq_pos] at hz_pos
  unfold H_post_simon at hz_pos
  rw [simon_amplitude_sum] at hz_pos
  by_cases hs : s = (fun _ => Qubit.zero)
  {
    subst hs
    apply dot_product_zero
  }
  {
    have h_nonempty : (Finset.univ.filter (fun x => f x = z)).Nonempty := by {
      by_contra h_empty
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      rw [Finset.filter_eq_empty_iff] at h_empty
      have h_sum_zero : ∑ x : {x // f x = z}, (-1 : ℂ)^(Qubit.toNat (dot_product x.1 y)) = 0 := by {
        apply Finset.sum_eq_zero
        intro x_subtype _
        have h_is_z : f x_subtype.val = z := x_subtype.property
        have h_is_not_z : f x_subtype.val ≠ z := by simp_all
        contradiction
      }
      rw [h_sum_zero] at hz_pos
      simp at hz_pos
    }
    rcases h_nonempty with ⟨x₀, hx₀_mem⟩
    rw [Finset.mem_filter] at hx₀_mem
    have hx₀ : f x₀ = z := hx₀_mem.2
    rw [simon_sum_grouping n m f s hf y z x₀ hx₀ hs] at hz_pos
    have h_interference : ((-1 : ℂ)^(Qubit.toNat (dot_product x₀ y)) + (-1 : ℂ)^(Qubit.toNat (dot_product (bs_xor x₀ s) y))) ≠ 0 := by {
      intro h_sum_zero
      rw [h_sum_zero, mul_zero] at hz_pos
      contradiction
    }
    exact phase_interference_zero y s x₀ h_interference
  }
}

-- running the full Simon's circuit on the zero state guarantees that any measured output y
-- will satisfy y·s = 0, allowing the classical computer to solve for the hidden string s
theorem simons_correctness {n m : ℕ} (f : BitString n → BitString m) (s : BitString n) (hf : simons_promise f s)
(hmn : m > 0 ∧ n > 0) :
∀ y : BitString n, prob_measure_y (〚simon n m f〛 (ket0n_0m n m)) y > 0 → dot_product y s = Qubit.zero := by {
  unfold simon
  simp [Qeval]
  rw [H_init_action_simon n m hmn.1 hmn.2]
  rw [oracle_action_simon n m hmn.1 f]
  exact simons_prob_measure_y f s hf
}
