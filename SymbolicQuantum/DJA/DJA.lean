import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumTactics

open QGate QCircuit

-- (Deutsch-Jozsa Algorithm)

def GlobalPhaseEq {n : ℕ}
  (ψ₁ ψ₂ : QState n) : Prop :=
  ∃ (c : ℂ), c ≠ 0 ∧ ψ₁ = c * ψ₂

infix:50 " ≡ₚ " => GlobalPhaseEq

-- phase equality
theorem Qeval_phase_eq {m : ℕ} (C : QCircuit m) (ψ₁ ψ₂ : QState m) :
  ψ₁ ≡ₚ ψ₂ → 〚C〛 ψ₁ ≡ₚ 〚C〛 ψ₂ := by {
  intro h
  unfold GlobalPhaseEq at h
  rcases h with ⟨θ, h_nonzero, h_eq⟩
  rw [h_eq]
  have h_linear : ∀ (φ : QState m), 〚C〛 (θ * φ) = θ * 〚C〛 φ := by {
    induction C with
    | skip =>
      simp [Qeval]
    | seq C1 C2 ih1 ih2 =>
      intro φ
      simp [Qeval]
      rw [ih1 φ]
      rw [ih2 (〚C1〛 φ)]
    | app g =>
      intro φ
      simp [Qeval]
      cases g <;> (simp [Qeval_gate] ; rename_i i)
      { congr }
      {
        unfold app_Y
        ring_nf
        funext bs
        cases hbi : (bs i) <;> qsimp [hbi]
      }
      {
        unfold app_Z
        ring_nf
        funext bs
        cases hbi: bs i <;> simp [hbi]
      }
      {
        unfold app_H
        ring_nf
        funext bs
        simp
        cases bs i <;> qsimp
      }
      {
        rename_i j
        unfold app_CNOT
        ring_nf
        funext bs
        split_ifs with hc1 <;> simp
      }
      {
        rename_i j
        unfold app_CZ
        ring_nf
        funext bs
        split_ifs with hc1
        { simp }
        { cases hbi : bs i <;> (cases hbj : bs j <;> simp [hbi, hbj]) }
      }
      {
        rename_i n
        unfold app_Uf app_X
        simp
        funext bs
        split_ifs with hc1 <;> simp [hc1]
      }
  }
  rw [h_linear ψ₂]
  use θ
}

def QRange_H (n start count : ℕ) : QCircuit n :=
  match count with
  | 0 => skip
  | k + 1 =>
    QRange_H n start k ≫
    if h : (start + k) < n then
      app (H ⟨start + k, h⟩)
    else
      skip

-- left state. forces (right) bits [k...n-1] to be zero
def mask_right {n : ℕ} (k : ℕ) (bs : BitString n) : BitString n :=
  fun i =>
    if i < k then
      bs i
    else
      Qubit.zero

-- right state. forces (left) bits [0...k-1] to be zero
def mask_left {n : ℕ} (k : ℕ) (bs : BitString n) : BitString n :=
  fun i =>
    if i < k then
      Qubit.zero
    else
      bs i

-- top-down
-- combines two states of size n at position k
def tensor_product {n : ℕ} (k_fin : Fin (n + 1)) (ψL : QState n) (ψR : QState n) : QState n :=
  let k := k_fin.val
  fun bs =>
    (ψL (mask_right k bs)) * (ψR (mask_left k bs))

notation ψL " ⊗[" k "] " ψR => tensor_product k ψL ψR

def basis_state {n : ℕ} (bs0 : BitString n) : QState n :=
  fun bs => if bs = bs0 then 1 else 0

def ket0 : QState 1 :=
  basis_state (fun _ => Qubit.zero)

def ket1 : QState 1 :=
  basis_state (fun _ => Qubit.one)

noncomputable def ketP : QState 1 :=
  fun (bs : BitString 1) =>
    let coeff := (1 / Real.sqrt 2 : ℂ)
    match bs 0 with
    | Qubit.zero => coeff
    | Qubit.one  => coeff

noncomputable def ketM : QState 1 :=
  fun (bs : BitString 1) =>
    let coeff := (1 / Real.sqrt 2 : ℂ)
    match bs 0 with
    | Qubit.zero => coeff
    | Qubit.one  => -coeff

def ket0n (n : ℕ) : QState n :=
  basis_state (fun _ => Qubit.zero)

noncomputable def ketPn (n : ℕ) : QState n :=
  fun _ => (1 / Real.sqrt (2 ^ n) : ℂ)

-- Lifts a state of size n into n+1 (relevant indices are 0 to n-1)
def embed_prefix {n : ℕ} (ψ : QState n) : QState (n + 1) :=
  fun bs =>
    ψ (fun i => bs ⟨i, by omega⟩)

-- Lifts a state of size 1 into size n+1 (relevant index is n)
def embed_last {n : ℕ} (ψ : QState 1) : QState (n + 1) :=
  fun bs =>
    ψ (fun _ => bs ⟨n, by omega⟩)

-- Lifts a state of size n into size m (relevant indices are 0 to n-1)
def embed_arb {n m : ℕ} (h : m ≥ n) (ψ : QState n) : QState m :=
  fun bs =>
    ψ (fun i => bs ⟨i, by omega⟩)

-- Lifts a bitstring of size n into size m+1 by appending 0's at the end
def embed_arb_zero {n m : ℕ} (x : BitString n) : BitString (m + 1) :=
  fun i =>
    if h : i < n then
      x ⟨i, h⟩
    else
      Qubit.zero

-- |0...0⟩ ⊗ |-⟩
noncomputable def ket0n_M (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ket0n n)
  let right_part := embed_last ketM
  left_part ⊗[⟨n, by omega⟩] right_part

-- |0...0⟩ ⊗ |1⟩
noncomputable def ket0n_1 (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ket0n n)
  let right_part := embed_last ket1
  left_part ⊗[⟨n, by omega⟩] right_part

-- |+...+⟩ ⊗ |->
noncomputable def ketPn_M (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ketPn n)
  let right_part := embed_last ketM
  left_part ⊗[⟨n, by omega⟩] right_part

def H_init_n (n : ℕ) : QCircuit (n+1) :=
  QRange_H (n+1) 0 n

def H_post_n (n : ℕ) : QCircuit (n+1) :=
  QRange_H (n+1) 0 n

def oracle_block (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  app (Uf f)

def deutsch_jozsa (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  H_init_n n ≫
  oracle_block n f ≫
  H_post_n n

def isConstant (n : ℕ) (f : BitString n → Bool) :=
  (∀ x, f x = true) ∨ (∀ x, f x = false)

def isBalanced (n : ℕ) (f : BitString n → Bool) : Prop :=
  Finset.sum Finset.univ (fun x => if f x then (-1 : ℂ) else 1) = 0

lemma Qeval_QRange_succ_split {n start k : ℕ} :
〚QRange_H n start (k + 1)〛 = 〚QRange_H n start k ≫ QRange_H n (start + k) 1〛 := by rfl

-- Disjoint commuting lemma for QRange_H
lemma QRange_H_disj_comm {n : ℕ} (start len target : ℕ)
(ht : target < n)
(h_disjoint : target ≥ start + len) :
∀ ψ, 〚QRange_H n start len〛 (〚app (H ⟨target, ht⟩)〛 ψ) =
〚app (H ⟨target, ht⟩)〛 (〚QRange_H n start len〛 ψ) := by {
  induction len generalizing start target ht with
  | zero =>
    simp [QRange_H, Qeval]
  | succ range_len ih =>
    intro ψ
    have h_range_len : start + range_len < n := by omega
    simp [QRange_H,Qeval,h_range_len,Qeval_gate]
    change 〚app (H ⟨start + range_len, h_range_len⟩)〛 (〚QRange_H n start range_len〛 (〚app (H ⟨target, ht⟩)〛 ψ)) =
      〚app (H ⟨target, ht⟩)〛 (〚app (H ⟨start + range_len, h_range_len⟩)〛 (〚QRange_H n start range_len〛 ψ))
    rw [ih start (target) (ht) (by omega)]
    simp [Qeval,Qeval_gate]
    rw [H_comm _ (by simp;omega)]
}

-- QRange can be split in reverse order of definition
lemma Qeval_QRange_succ_split_rev {n start k : ℕ} (h : start + k < n) :
  〚QRange_H n start (k + 1)〛 = 〚QRange_H n (start + k) 1 ≫ QRange_H n start k〛 := by {
  rw [Qeval_QRange_succ_split]
  have hc1 : start + k < n := by omega
  simp [QRange_H, hc1, Qeval, Qeval_gate]
  funext ψ
  change 〚app (H ⟨start + k, h⟩)〛 (〚QRange_H n start k〛 ψ) =
    〚QRange_H n start k〛 (〚app (H ⟨start + k, h⟩)〛 ψ)
  rw [QRange_H_disj_comm]
  exact Nat.le_refl _
}

lemma embed_prefix_ket0n_succ {n : ℕ} :
embed_prefix (ket0n (n + 1)) =
(embed_prefix (embed_prefix (ket0n n))) ⊗[⟨n, by omega⟩] (embed_prefix (embed_last ket0)) := by
  funext bs
  unfold tensor_product embed_prefix embed_last mask_left mask_right ket0n ket0 basis_state
  simp
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    exfalso
    apply hc3
    funext i
    exact congr_fun hc1 ⟨i, by omega⟩
  }
  {
    exfalso
    apply hc2
    funext x
    exact congr_fun hc1 ⟨n, by omega⟩
  }
  {
    exfalso
    apply hc1
    apply congr_fun at hc4
    apply congr_fun at hc5
    funext k
    by_cases h : k = n
    {
      have : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.eq_of_val_eq h
      rw [this]
      exact hc4 ⟨0, Nat.zero_lt_one⟩
    }
    exact hc5 ⟨k, by omega⟩
  }

-- QRange_H applied to one state times another is equivalent to applying to
-- one state then multiplying by the other
lemma QRange_H_distrib_disjoint (m k : ℕ) (hk_bound : k ≤ m + 1) :
  ∀ (f g : BitString (m+1) → ℂ),
  (∀ (bs : BitString (m+1)) (v : Qubit) (j : Fin (m+1)),
     (j : ℕ) < k → g (fun i => if i = j then v else bs i) = g bs) →
  〚QRange_H (m + 1) 0 k〛 (fun bs => f bs * g bs)
  = (fun bs => (〚QRange_H (m + 1) 0 k〛 f) bs * g bs) := by {
  induction k with
  | zero =>
    simp [QRange_H, Qeval]
  | succ k' ih =>
    intros f g h_ignore
    have hk' : k' < m + 1 := by omega
    rw [QRange_H]
    simp [hk', Qeval, Qeval_gate]
    rw [ih (by omega) f g]
    {
      funext bs
      have h_inv_at_k : ∀ (v : Qubit), g (fun i ↦ if i = ⟨k', hk'⟩ then v else bs i) = g bs := by {
        intro v
        apply h_ignore bs v ⟨k', hk'⟩
        simp
      }
      simp [app_H, h_inv_at_k]
      cases hk' : bs ⟨k', hk'⟩ <;> ring_nf
    }
    {
      intros bs v j hj
      apply h_ignore bs v j
      exact Nat.lt_succ_of_lt hj
    }
}

lemma QRange_H_involutive_general (m n : ℕ) (h_bound : n ≤ m + 1) :
  ∀ (ψ : QState (m + 1)),
  〚QRange_H (m+1) 0 n〛 (〚QRange_H (m+1) 0 n〛 ψ) = ψ := by {
  induction n with
  | zero =>
    intro ψ
    simp [QRange_H, Qeval]
  | succ k ih =>
    intro ψ
    nth_rw 1 [Qeval_QRange_succ_split_rev (by linarith)]
    nth_rw 1 [Qeval]
    have hk : k < m + 1 := by omega
    simp [QRange_H, hk, Qeval, Qeval_gate]
    rw [H_involutive, ih (by omega)]
}

-- /-
-- Generalized lemma for H_init_ket0n_M
-- Necessary for induction on n to work (not possible otherwise since IH and goal types don't match)
lemma H_init_ket0n_M_gen (n m : ℕ) (h : n ≤ m) :
(〚QRange_H (m+1) 0 n〛 (embed_arb (by simp [h]) (ket0n_M n))) = embed_arb (by simp [h]) (ketPn_M n) := by {
  induction n generalizing m with
  | zero =>
    unfold QRange_H ket0n_M ketPn_M Qeval
    unfold embed_prefix embed_last tensor_product ket0n ketPn ketM
    unfold basis_state mask_left mask_right
    simp
  | succ n ih =>
    rw [Qeval_QRange_succ_split]
    unfold Qeval
    unfold embed_arb
    unfold ket0n_M
    unfold tensor_product
    unfold embed_arb at ih
    unfold ket0n_M at ih
    unfold embed_prefix embed_last at ih
    unfold tensor_product at ih
    unfold mask_left mask_right at ih
    simp [embed_prefix_ket0n_succ]
    unfold mask_left mask_right embed_prefix embed_last
    unfold ketPn_M ketPn embed_prefix embed_last tensor_product mask_left mask_right at ih ⊢
    have hq : n < m+1 := by omega
    have hq' : n ≤ m := by omega
    simp [QRange_H, Qeval, hq, Qeval_gate] at h ⊢
    have hcon1 :
      (fun (bs : BitString (m+1)) ↦
    ((ket0n n fun i ↦ if ↑i < n + 1 then bs ⟨i, by omega⟩ else Qubit.zero) * ket0 fun x ↦ bs ⟨n, by omega⟩) *
      ketM fun x ↦ bs ⟨n + 1, by omega⟩) =
      (fun bs ↦
    (ket0 fun x ↦ bs ⟨n, by omega⟩) * ((ket0n n fun i ↦ bs ⟨i, by omega⟩) *
      ketM fun x ↦ bs ⟨n + 1, by omega⟩)) := by {
        funext bs
        unfold ket0n ket0 ketM basis_state
        simp
        split_ifs with hc1 hc2 hc3 hc4 <;> try simp
        {
          exfalso
          apply hc3
          funext i
          have := congr_fun hc2 i
          simp [Nat.lt_succ_of_lt (Fin.is_lt i)] at this
          exact this
        }
        {
          exfalso
          apply hc2
          funext i
          simp [Nat.lt_succ_of_lt (Fin.is_lt i)]
          exact congr_fun hc4 i
        }
    }
    rw [hcon1]
    unfold ketM at ih ⊢
    simp at ih ⊢
  -- [STEP 1: Define Components]
    let psi_prefix  := fun (bs : BitString (m+1)) => ket0n n (fun i => bs ⟨i, by omega⟩)
    let psi_target  := fun (bs : BitString (m+1)) => ket0 (fun _ => bs ⟨n, hq⟩)
    let psi_ancilla := fun (bs : BitString (m+1)) => ketM (fun _ => bs ⟨n + 1, by omega⟩)
    -- [STEP 2: Align Goal with Definitions]
    -- Goal: Target * (Prefix * Ancilla)
    -- Want: Prefix * Target * Ancilla
    have h_align_goal :
      (fun bs => (ket0 fun x => bs ⟨n, hq⟩) * ((ket0n n fun i => bs ⟨i, by omega⟩) * match bs ⟨n + 1, by omega⟩ with | Qubit.zero => (Real.sqrt 2)⁻¹ | Qubit.one => -((Real.sqrt 2 : ℂ))⁻¹))
      =
      (fun bs => psi_prefix bs * psi_target bs * psi_ancilla bs) := by {
      funext bs
      unfold psi_prefix psi_target psi_ancilla ketM
      ring_nf
    }
    rw [h_align_goal]
    -- [STEP 3: Distributivity via General Lemma]
    have h_distrib :
      〚QRange_H (m + 1) 0 n〛 (fun bs => psi_prefix bs * psi_target bs * psi_ancilla bs)
      = (fun bs => (〚QRange_H (m + 1) 0 n〛 psi_prefix) bs * psi_target bs * psi_ancilla bs) := by {
      simp [mul_assoc]
      apply QRange_H_distrib_disjoint m n (by omega)
      intros bs v i hi
      unfold psi_target psi_ancilla
      simp
      congr
      {
        funext k
        split_ifs with hc
        {
          exfalso
          cases hc
          simp at hi
        }
        rfl
      }
      {
        funext k
        split_ifs with hc
        {
          exfalso
          cases hc
          simp at hi
        }
        rfl
      }
    }
    rw [h_distrib]
    -- [STEP 4: Resolve Inner Circuit using IH]
    let psi_prefix_transformed := fun (bs : BitString (m+1)) => ketPn n (fun i => bs ⟨i, by omega⟩)
    have h_transform : 〚QRange_H (m + 1) 0 n〛 psi_prefix = psi_prefix_transformed := by {
      specialize ih m (by linarith)
      let factor := fun (bs : BitString (m+1)) =>
        match bs ⟨n, by omega⟩ with
        | Qubit.zero => ((Real.sqrt 2) : ℂ)⁻¹
        | Qubit.one  => -((Real.sqrt 2) : ℂ)⁻¹
      have h_linear : 〚QRange_H (m + 1) 0 n〛 (fun bs => psi_prefix bs * factor bs)
                      = (fun bs => (〚QRange_H (m + 1) 0 n〛 psi_prefix) bs * factor bs) := by {
        apply QRange_H_distrib_disjoint m n (by omega)
        intros bs v i hi
        unfold factor
        simp only []
        rw [if_neg]
        intro hcon
        cases hcon
        simp at hi
      }
      rw [h_linear] at ih
      funext bs
      have ih_bs := congr_fun ih bs
      simp at ih_bs
      have factor_nonzero : factor bs ≠ 0 := by {
        intro h_zero
        unfold factor at h_zero
        split at h_zero <;> simp at h_zero
      }
      have h_eq := mul_right_cancel₀ factor_nonzero ih_bs
      unfold psi_prefix_transformed ketPn at *
      have : (↑√(2 ^ n))⁻¹ = psi_prefix_transformed bs := by {
        unfold psi_prefix_transformed
        unfold ketPn
        simp
      }
      exact Eq.trans h_eq this
    }
    rw [h_transform]
    -- [STEP 5: Evaluate the Final Gate (H at idx n)]
    let psi_target_transformed := fun (bs : BitString (m+1)) => ketP (fun _ => bs ⟨n, hq⟩)
    have h_gate_eval :
      app_H (fun bs => psi_prefix_transformed bs * psi_target bs * psi_ancilla bs) ⟨n, by omega⟩
      = (fun bs => psi_prefix_transformed bs * psi_target_transformed bs * psi_ancilla bs) := by {
      funext bs
      unfold app_H
      unfold psi_prefix_transformed psi_target psi_target_transformed psi_ancilla
      unfold ketPn ketP ket0 ketM basis_state
      simp
      cases hn : bs ⟨n, hq⟩ <;> (cases bs ⟨n + 1, by omega⟩) <;> simp
      {
        intros _
        contradiction
      }
      {
        split_ifs with hc1
        contradiction
        simp
      }
      {
        intros _
        contradiction
      }
      {
        split_ifs with hc1
        contradiction
        simp
      }
    }
    rw [h_gate_eval]
    -- [STEP 6: Final Steps]
    funext bs
    unfold psi_prefix_transformed psi_target_transformed psi_ancilla
    unfold ketPn ketP ketM
    rw [pow_succ' 2 n]
    cases bs ⟨n + 1, by omega⟩ <;> (cases bs ⟨n, hq⟩ <;> simp)
}
-- -/

-- /-
-- step 1 (initial hadamards)
lemma H_init_action (n : ℕ) :
〚H_init_n n〛 (ket0n_M n) = ketPn_M n :=
H_init_ket0n_M_gen n n (Nat.le_refl n) -- generalized lemma with m = n

lemma H_init_eq_post (n : ℕ) : H_init_n n = H_post_n n := by rfl

-- step 2 (final hadamards) - reverse direction
lemma H_post_action (n : ℕ) :
〚H_post_n n〛 (ketPn_M n) = ket0n_M n := by {
  rw [←H_init_eq_post n]
  rw [←H_init_action n]
  unfold H_init_n
  exact QRange_H_involutive_general n n (Nat.le_succ n) (ket0n_M n)
}

-- step 3 (oracle action for constant functions)
lemma oracle_constant_kickback {n : ℕ} (f : BitString n → Bool) (hf : isConstant n f) :
〚oracle_block n f〛 (ketPn_M n) ≡ₚ ketPn_M n := by {
  unfold oracle_block
  unfold isConstant at hf
  cases hf with
  | inl ht =>
    simp [Qeval, Qeval_gate]
    unfold app_Uf app_X
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
    unfold app_Uf
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
  rw [H_init_action]
  rw [←H_post_action n]
  apply Qeval_phase_eq
  exact oracle_constant_kickback f hf
}

-- DJA balanced case

-- phase kickback state
noncomputable def ket_f_kickback {n : ℕ} (f : BitString n → Bool) : QState (n + 1) :=
  fun bs =>
  (1 / Real.sqrt (2^(n+1)) : ℂ) * (if f (fun i => bs ⟨i, by omega⟩) then -1 else 1) *
  (match bs ⟨n, Nat.lt_add_one n⟩ with
    | Qubit.zero => 1
    | Qubit.one  => -1
  )

-- oracle action for balanced case (sending state to phase kickback state)
lemma oracle_balanced_action {n : ℕ} (f : BitString n → Bool) :
〚oracle_block n f〛 (ketPn_M n) ≡ₚ ket_f_kickback f := by {
  unfold oracle_block
  unfold ket_f_kickback
  simp [Qeval, Qeval_gate]
  unfold app_Uf app_X
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

/- balanced correctness lemmas -/

-- helper
abbrev bs_pad  {n : ℕ} (x : BitString n) (b : Qubit) : BitString (n + 1) :=
  fun i => if h : ↑i < n then x ⟨i, h⟩ else b

-- reasoning about disjoint sums
lemma sum_bitstring_split_last (n : ℕ) (ψ : BitString (n + 1) → ℂ) :
  ∑ x : BitString (n + 1), ψ x =
  (∑ x : BitString n, ψ (bs_pad x Qubit.zero)) +
  (∑ x : BitString n, ψ (bs_pad x Qubit.one)) := by {
  -- define isomorphism
  let iso : BitString n × Bool ≃ BitString (n + 1) := {
    toFun := fun ⟨x, b⟩ => bs_pad x (if b then Qubit.one else Qubit.zero),
    invFun := fun y => (fun i => y ⟨i, by omega⟩, y ⟨n, by omega⟩ = Qubit.one),
    left_inv := by
      intro ⟨x, b⟩
      simp [bs_pad]
    right_inv := by
      intro y
      funext i
      simp [bs_pad]
      split_ifs with h_lt
      {
        intro h
        have : i = n := Nat.eq_of_le_of_lt_succ h i.prop
        rw [←h_lt]
        congr
        exact this.symm
      }
      {
        intro h
        have : i = n := Nat.eq_of_le_of_lt_succ h i.prop
        have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext this
        rw [this]
        cases hy : y ⟨n, (by simp)⟩
        { rfl }
        { contradiction }
      }
  }
  trans ∑ p : BitString n × Bool, ψ (iso p)
  { simp_rw [Fintype.sum_equiv iso] }
  {
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Fintype.sum_bool]
    simp [iso, Equiv.coe_fn_mk, add_comm]
  }
}

-- generalized lemma
-- disjoint indices commute through QRange_H
lemma QRange_H_flip_invariant_gen (m k : ℕ) (n_idx : Fin (m + 1)) (h_disjoint : k ≤ n_idx)
  (ψ : QState (m + 1)) (b : BitString (m + 1)) (hb : b n_idx = Qubit.one) :
  let ψ_masked := fun bs ↦ if bs n_idx = Qubit.one then ψ bs else 0
  let ψ_shifted := fun bs ↦ ψ (Function.update bs n_idx Qubit.one)
  (〚QRange_H (m + 1) 0 k〛 ψ_masked) b = (〚QRange_H (m + 1) 0 k〛 ψ_shifted) (Function.update b n_idx Qubit.zero) := by {
  induction k generalizing m b ψ hb with
  | zero =>
    simp [QRange_H, Qeval]
    split_ifs
    congr
    funext i
    by_cases h : i = n_idx
    { rw [h, Function.update_self, ←hb] }
    { rw [Function.update_apply, if_neg h] }
  | succ k' ih =>
    have h_bound : k' < m + 1 := by omega
    have h_neq : (⟨k', h_bound⟩ : Fin (m + 1)) ≠ n_idx := by {
      apply ne_of_lt
      exact h_disjoint
    }
    simp [QRange_H, Qeval, h_bound, Qeval, Qeval_gate, app_H, Function.update_apply, if_neg h_neq]
    cases b ⟨k', h_bound⟩
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
(〚H_post_n n〛 (ket_f_kickback f)) (fun _ => Qubit.zero) = 0 := by {
  unfold H_post_n
  rw [QRange_H_sum_property n n (by rfl)]
  unfold ket_f_kickback embed_arb_zero
  unfold isBalanced at hf
  simp [Finset.mul_sum]
  have ht2 : (((↑√(2 ^ n) : ℂ))⁻¹ * (↑√(2 ^ (n + 1)))⁻¹) = ((↑√(2 ^ (2*n+1)))⁻¹) := by {
    field_simp
    have : ((2 ^ (2 * n + 1)) : ℝ) = (2 ^ n) * (2 ^ (n + 1)) := by {
      rw [←pow_add]
      congr 1
      omega
    }
    simp[this]
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
  rw [H_init_action]
  have h_equiv : 〚H_post_n n〛 (〚oracle_block n f〛 (ketPn_M n)) ≡ₚ 〚H_post_n n〛 (ket_f_kickback f) := by {
    apply Qeval_phase_eq
    exact oracle_balanced_action f
  }
  rcases h_equiv with ⟨c, hc_nonzero, h_state_eq⟩
  simp [h_state_eq, hc_nonzero]
  exact balanced_H_kickback_zero f hf
}
