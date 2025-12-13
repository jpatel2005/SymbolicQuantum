import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval

open QGate QCircuit

-- (Deutsch-Jozsa Algorithm)

def GlobalPhaseEq {n : ℕ}
  (ψ₁ ψ₂ : QState n) : Prop :=
  ∃ (c : ℂ), c ≠ 0 ∧ ψ₁ = c * ψ₂

infix:50 "≡ₚ " => GlobalPhaseEq

-- TODO need to modify this to include a lower bound as well
-- might need to use two different definitions (fold left vs fold right) to make proofs easier
-- can also prove equality betwen them at some point (in theory)
def QFold_H {n : ℕ} (k : ℕ) : QCircuit n :=
  match k with
    | 0 => skip
    | i + 1 =>
      QFold_H i ≫
      if h : i < n then
        app (H ⟨i, h⟩)
      else
        skip

def QRange_H {n : ℕ} (start : ℕ) (count : ℕ) : QCircuit n :=
  match count with
  | 0 => skip
  | k + 1 =>
    QRange_H (n := n) start k ≫
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

-- Lifts a state of size 1 into size n+1 (relevant indices are 0 to n)
def embed_last {n : ℕ} (ψ : QState 1) : QState (n + 1) :=
  fun bs =>
    ψ (fun _ => bs ⟨n, by omega⟩)

-- Lifts a state of size n into size m (relevant indices are 0 to n-1)
def embed_last_arb {n m : ℕ} (h : m ≥ n) (ψ : QState n) : QState m :=
  fun bs =>
    ψ (fun i => bs ⟨i, by omega⟩)

-- |0...0⟩ ⊗ |-⟩
noncomputable def ket0n_M (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ket0n n)
  let right_part := embed_last ketM
  left_part ⊗[⟨n, by omega⟩] right_part

-- |+...+> ⊗ |->
noncomputable def ketPn_M (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ketPn n)
  let right_part := embed_last ketM
  left_part ⊗[⟨n, by omega⟩] right_part

def H_init_n (n : ℕ) : QCircuit (n+1) :=
  QRange_H 0 n

def H_post_n (n : ℕ) : QCircuit (n+1) :=
  QRange_H 1 n -- double check this when you do the proofs

def oracle_block (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  app (Uf f)

def deutsch_jozsa (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  H_init_n n ≫
  oracle_block n f ≫
  H_post_n n

def isConstant (n : ℕ) (f : BitString n → Bool) :=
  (∀ x, f x = true) ∨ (∀ x, f x = false)

def isBalanced (n : ℕ) (f : BitString n → Bool) [Fintype (BitString n)] :=
  Finset.sum Finset.univ (fun x => if f x then (1 : ℕ) else (0 : ℕ)) = (Fintype.card (BitString n)) / 2

lemma Qeval_QRange_succ_split {n start k : ℕ} :
〚QRange_H (n := n) start (k + 1)〛 = 〚QRange_H (n := n) start k ≫ QRange_H (n := n) (start + k) 1〛 := by rfl

/-
lemma app_H_distrib_left {n : ℕ} (k : Fin (n + 1)) (i : Fin n) (hi : ⟨i, by omega⟩ < k)
  (ψL ψR : QState n) :
  (app_H (ψL ⊗[k] ψR) i) = (app_H ψL i) ⊗[k] ψR := by {
  -- This proof requires unfolding tensor_product and app_H.
  -- You show that mask_left hides index 'i' from ψR because i < k.
  sorry
}

lemma QRange_distrib_tensor {n : ℕ} (ψL : QState n) (ψR : QState n) :
  -- Applying H to 0..n-1
  〚QRange_H (n := n) 0 n〛 (ψL ⊗[⟨n, by omega⟩] ψR)
  =
  -- Is the same as applying it to ψL only
  (〚QRange_H (n := n) 0 n〛 ψL) ⊗[⟨n, by omega⟩] ψR := by {
  induction n with
  | zero => simp [QRange_H, Qeval]
  | succ k ih =>
    rw [Qeval_QRange_succ_split]
    simp [Qeval]
    -- rw [ih] -- Inner range distributes
    -- Outer gate distributes (Lemma A) because k < k+1
    -- rw [app_H_distrib_left]
    -- exact Nat.lt_succ_self k
    sorry
}

lemma QRange_transform_prefix {n : ℕ} :
  〚QRange_H (n := n+1) 0 n〛 (embed_prefix (ket0n n)) = embed_prefix (ketPn n) := by {
  -- This proof is purely about mapping |0..0> to |+..+>
  -- It requires some algebra with embeddings.
  sorry
}
-/

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
    {
      exact hc5 ⟨k, by omega⟩
    }
  }

-- /-
lemma H_init_ket0n_M (n m : ℕ) (h : n ≤ m) :
(〚QRange_H (n := m+1) 0 n〛 (embed_last_arb (by simp [h]) (ket0n_M n))) = embed_last_arb (by simp [h]) (ketPn_M n) := by {
  induction n generalizing m with
  | zero =>
    unfold QRange_H ket0n_M ketPn_M Qeval
    simp
    unfold embed_prefix embed_last tensor_product ket0n ketPn ketM
    unfold basis_state mask_left mask_right
    funext bs
    simp
  | succ n ih =>
    rw [Qeval_QRange_succ_split]
    unfold Qeval
    simp
    -- have h' : n ≤ m := by linarith
    -- have h'' : n+1+1 ≤ m+1 := by linarith

    unfold embed_last_arb
    unfold ket0n_M

    unfold embed_last_arb at ih
    unfold ket0n_M at ih


    -- unfold embed_last_arb at ih
    -- unfold ket0n_M at ih

    rw [embed_prefix_ket0n_succ]

    sorry
}
-- -/

theorem DJA_correctness_constant {n : ℕ} (f : BitString n → Bool) (hf: isConstant n f):
〚deutsch_jozsa n f〛 (ket0n_M n) ≡ₚ (ket0n_M n) := by {
  unfold deutsch_jozsa
  unfold Qeval
  unfold H_init_n
  -- rw [H_init_ket0n_M]
  sorry
}


/-
lemma QFold_H_succ_eq {n : ℕ} (k : ℕ) (hk : k < n) :
QFold_H (k + 1) = QFold_H k ≫ app (H ⟨k, hk⟩) := by {
  nth_rw 1 [QFold_H]
  simp [hk]
}
-/

/-
-- induction on n seems hard
lemma H_init_ket0n_M (n m : ℕ) (h : n ≤ m) : (〚H_init_n m〛 (embed_last_arb (by simp [h]) (ket0n_M n))) = (embed_last_arb (by simp [h]) (ketPn_M n)) := by {
  unfold H_init_n
  induction n generalizing m with
  | zero =>
    unfold ket0n_M ketPn_M
    repeat unfold ket0n ketPn
    unfold tensor_product mask_left mask_right
    repeat unfold basis_state embed_last embed_prefix
    unfold ketM
    simp
    unfold embed_last_arb
    simp
    funext bs
    sorry
  | succ k ih =>
    -- rw [QFold_H_succ_eq k (by linarith)]
    -- unfold Qeval
    -- unfold ket0n_M
    -- simp
    sorry
}
-/

/-
lemma H_init_ket0n_M (n m : ℕ) (h : n ≤ m) : (〚H_init_n m〛 (embed_last_arb (by simp [h]) (ket0n_M n))) = (embed_last_arb (by simp [h]) (ketPn_M n)) := by {
  unfold H_init_n
  induction m generalizing n with
  | zero =>
    unfold QFold_H Qeval
    unfold ketPn_M ket0n_M
    unfold tensor_product embed_prefix embed_last embed_last_arb mask_left mask_right
    unfold ket0n ketPn ketM basis_state
    simp
    funext bs
    split_ifs with hc1
    {
      have : n = 0 := by linarith
      simp [this]
    }
    {
      exfalso
      apply hc1
      funext k
      split_ifs with hc2 <;> try rfl
      {
        have : k < 0 := by linarith
        contradiction
      }
    }
  | succ k ih =>
    sorry
}
-/


-- [NOTE]: H_init old proofs above

/-

noncomputable def ket0n_M (n : ℕ) : QState (n+1) :=
  (ket0n n) ⊗ ketM

noncomputable def ketPn (n : ℕ) : QState n :=
  fun (_ : BitString n) => (1 / Real.sqrt (2 ^ n) : ℂ)

noncomputable def ketPn_M (n : ℕ) : QState (n+1) :=
  (ketPn n) ⊗ ketM

-- def H_all_n (n : ℕ) : QCircuit n :=
  -- List.foldl (fun acc q => (acc ≫ app (H q))) skip (List.finRange n)

def H_init_n (n : ℕ) : QCircuit (n+1) :=
  QFold_H n

def H_post_n (n : ℕ) : QCircuit (n+1) :=
  H_init_n n

def oracle_block (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  app (Uf f)

def deutsch_jozsa (n : ℕ) (f : BitString n → Bool) : QCircuit (n+1) :=
  H_init_n n ≫
  oracle_block n f ≫
  H_post_n n

def isConstant (n : ℕ) (f : BitString n → Bool) :=
  (∀ x, f x = true) ∨ (∀ x, f x = false)

def isBalanced (n : ℕ) (f : BitString n → Bool) [Fintype (BitString n)] :=
  Finset.sum Finset.univ (fun x => if f x then (1 : ℕ) else (0 : ℕ)) = (Fintype.card (BitString n)) / 2

lemma ket0n_succ_eq_ket0n_tensor_ket0 {n : ℕ} :
ket0n (n + 1) = ket0n n ⊗ ket0 := by {
  induction n with
  | zero =>
    unfold ket0n tensor_product ket0
    funext bs
    unfold basis_state ket0n
    simp
  | succ n ih =>
    unfold ket0n tensor_product ket0 basis_state
    funext bs
    rw [ih]
    simp
    split_ifs with hc1 hc2
    {
      unfold tensor_product ket0 basis_state
      simp_all
    }
    {
      unfold tensor_product ket0 basis_state
      simp_all
    }
    rfl
}

/-
lemma ket0n_succ_eq_ket0n_tensor_ket0 {n : ℕ} :
ket0n (n + 1) = (embed_prefix (ket0n n)) ⊗[⟨n, by omega⟩] (embed_last ket0) := by {
  funext bs
  unfold tensor_product embed_prefix embed_last mask_left mask_right ket0n ket0 basis_state
  simp
  split_ifs with hc1 hc2 hc3 hc4 hc5 <;> try rfl
  {
    simp_all
  }
  {
    simp_all
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
    {
      exact hc5 ⟨k, by omega⟩
    }
  }
}
-/

lemma QFold_H_succ_eq {n : ℕ} (k : ℕ) (hk : k < n) :
QFold_H (k + 1) = QFold_H k ≫ app (H ⟨k, hk⟩) := by {
  nth_rw 1 [QFold_H]
  simp [hk]
}

lemma QFold_H_correct (k : ℕ) {m : ℕ} (ψ : QState m) :
  〚QFold_H k〛 (ket0n k ⊗ ψ) = (ketPn k ⊗ ψ) := by {
  induction k generalizing m ψ with
  | zero =>
    unfold QFold_H ket0n ketPn
    simp
    rfl
  | succ k ih =>
    rw [QFold_H_succ_eq k (by omega)]
    unfold Qeval
    -- rw [ket0n_succ_eq_ket0n_tensor_ket0]
    sorry
}

lemma H_init_ket0n_M (n : ℕ) : (〚H_init_n n〛 (ket0n_M n)) = ketPn_M n := by {
  induction n with
  | zero =>
    unfold H_init_n ket0n_M ketPn_M ket0n QFold_H Qeval
    simp
    funext bs
    unfold tensor_product ketM ketPn
    simp
  | succ n ih =>
    unfold H_init_n
    unfold ket0n_M ketPn_M
    exact QFold_H_correct (n+1) ketM
}

theorem DJA_correctness_constant {n : ℕ} (f : BitString n → Bool) (hf: isConstant n f):
〚deutsch_jozsa n f〛 (ket0n_M n) ≡ₚ
(ket0n (n+1)) := by {
    unfold deutsch_jozsa
    unfold Qeval
    rw [H_init_ket0n_M]
    unfold Qeval
    sorry
}
-/
