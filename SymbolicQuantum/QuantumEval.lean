import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import SymbolicQuantum.QuantumStates

inductive QGate (n : ℕ)
| X : (Fin n) → QGate n
| Y : (Fin n) → QGate n
| Z : (Fin n) → QGate n
| H : (Fin n) → QGate n
| CNOT : (Fin n) → (Fin n) → QGate n
| CZ : (Fin n) → (Fin n) → QGate n
| Uf : (BitString n -> Bool) -> Fin n -> QGate n

inductive QCircuit (n : ℕ)
| skip : QCircuit n
| app : QGate n → QCircuit n
| seq : QCircuit n → QCircuit n → QCircuit n

open QGate QCircuit

noncomputable def Qeval_gate {n : ℕ} : QGate n → QState n → QState n
| (X k)      => fun ψ => app_X ψ k
| (Y k)      => fun ψ => app_Y ψ k
| (Z k)      => fun ψ => app_Z ψ k
| (H k)      => fun ψ => app_H ψ k
| (CNOT i j) => fun ψ => app_CNOT ψ i j
| (CZ i j)   => fun ψ => app_CZ ψ i j
| (Uf f k)   => fun ψ => app_Uf ψ f k

noncomputable def Qeval {n : ℕ} : QCircuit n → QState n → QState n
| skip      => fun ψ => ψ
| (app g)   => fun ψ => Qeval_gate g ψ
| (seq a b) => fun ψ => (Qeval b) ((Qeval a) ψ)

def equiv {n : ℕ} (c1 c2 : QCircuit n) : Prop :=
  ∀ ψ, Qeval c1 ψ = Qeval c2 ψ

-- Define operator notation
notation "〚" c "〛" => Qeval c
infix:50 " ≡ " => equiv
infixr:55 " ≫ " => seq

-- Define equiv as a relational operator

theorem equiv_def {n : ℕ} (c1 c2 : QCircuit n) : (c1 ≡ c2) ↔ ∀ ψ, 〚 c1 〛 ψ = 〚 c2 〛 ψ := by rfl

@[refl]
theorem equiv_refl {n : ℕ} (c : QCircuit n) : c ≡ c := by {
  intro ψ
  rfl
}

@[symm]
theorem equiv_symm {n : ℕ} {c₁ c₂ : QCircuit n} : (c₁ ≡ c₂) → (c₂ ≡ c₁) := by {
  intro h ψ
  rw [h]
}

@[trans]
theorem equiv_trans {n : ℕ} {c₁ c₂ c₃ : QCircuit n} : (c₁ ≡ c₂) → (c₂ ≡ c₃) → (c₁ ≡ c₃) := by {
  intros h₁ h₂ ψ
  rw [h₁, h₂]
}

theorem seq_assoc {n : ℕ} (a b c : QCircuit n) :
  (a ≫ b) ≫ c ≡ a ≫ (b ≫ c) := by {
  intros ψ
  dsimp [Qeval]
}

/-

instance equiv_Equivalence {n : ℕ} : Equivalence (@equiv n) where
  refl := equiv_refl
  symm := @equiv_symm n
  trans := @equiv_trans n

def QCircuit_Setoid (n : ℕ) : Setoid (QCircuit n) :=
  { r := equiv, iseqv := ⟨equiv_refl, @equiv_symm n, @equiv_trans n⟩ }

-/

-- sequence and skip theorems

theorem seq_skip_left {n : ℕ} (c : QCircuit n) : (skip ≫ c) ≡ c := by {
  intro ψ
  dsimp [Qeval]
}

theorem seq_skip_right {n : ℕ} (c : QCircuit n) : (c ≫ skip) ≡ c := by {
  intro ψ
  dsimp [Qeval]
}

-- sequence congruence theorems

theorem seq_congr_left {n : ℕ} {c1 c1' c2 : QCircuit n} : (c1 ≡ c1') → (c1 ≫ c2) ≡ (c1' ≫ c2) := by {
  intro h ψ
  dsimp [Qeval]
  rw [h]
}

theorem seq_congr_right {n : ℕ} {c1 c2 c2' : QCircuit n} : (c2 ≡ c2') → (c1 ≫ c2) ≡ (c1 ≫ c2') := by {
  intro h ψ
  dsimp [Qeval]
  rw [h]
}

theorem seq_congr {n : ℕ} {a a' b b' : QCircuit n} : (a ≡ a') → (b ≡ b') → (a ≫ b) ≡ (a' ≫ b') := by {
  intros ha hb ψ
  rw [seq_congr_left ha, seq_congr_right hb]
}

-- sequence gate involution theorems

theorem X_X_equiv_skip {n : ℕ} (k : Fin n) : (app (X k)) ≫ (app (X k)) ≡ skip := by {
  intro ψ
  dsimp [Qeval]
  exact X_involutive ψ k
}

theorem Y_Y_equiv_skip {n : ℕ} (k : Fin n) : (app (Y k)) ≫ (app (Y k)) ≡ skip := by {
  intro ψ
  dsimp [Qeval]
  exact Y_involutive ψ k
}

theorem Z_Z_equiv_skip {n : ℕ} (k : Fin n) : (app (Z k)) ≫ (app (Z k)) ≡ skip := by {
  intro ψ
  dsimp [Qeval]
  exact Z_involutive ψ k
}

theorem H_H_equiv_skip {n : ℕ} (k : Fin n) : (app (H k)) ≫ (app (H k)) ≡ skip := by {
  intro ψ
  dsimp [Qeval]
  exact H_involutive ψ k
}

theorem CNOT_CNOT_equiv {n : ℕ} {i j : Fin n} (h : i ≠ j) : (app (CNOT i j) ≫ app (CNOT i j)) ≡ skip := by {
  intro ψ
  dsimp [Qeval]
  exact CNOT_involutive ψ i j h
}

-- hadamard theorems

theorem H_X_H_eq_Z {n : ℕ} (k : Fin n) : (app (H k)) ≫ (app (X k)) ≫ (app (H k)) ≡ (app (Z k)) := by {
  intro ψ
  dsimp [Qeval]
  exact HXH_Z ψ k
}

theorem H_Z_H_eq_X {n : ℕ} (k : Fin n) : (app (H k)) ≫ (app (Z k)) ≫ (app (H k)) ≡ (app (X k)) := by {
  intro ψ
  dsimp [Qeval]
  exact HZH_X ψ k
}

theorem H_CNOT_H_eq_CZ {n : ℕ} {i j : Fin n} (hij : i ≠ j) : ((app (H j)) ≫ (app (CNOT i j)) ≫ (app (H j))) ≡ (app (CZ i j)) := by {
  intro ψ
  dsimp [Qeval]
  exact H_CNOT_H_CZ ψ hij
}

theorem H_CZ_H_eq_CNOT {n : ℕ} {i j : Fin n} (hij : i ≠ j) : ((app (H j)) ≫ (app (CZ i j)) ≫ (app (H j))) ≡ (app (CNOT i j)) := by {
  intro ψ
  dsimp [Qeval]
  exact H_CZ_H_CNOT ψ hij
}

-- distinct qubit sequence commutivity theorems

theorem X_comm_Z {n : ℕ} {i j : Fin n} (hij : i ≠ j) : (app (X i)) ≫ (app (Z j)) ≡ (app (Z j)) ≫ (app (X i)) := by {
  intro ψ
  dsimp [Qeval]
  funext bs
  unfold Qeval_gate app_X app_Z
  simp
  have hij' : j ≠ i := by rw [ne_eq]; exact hij.symm
  cases hj : bs j <;> simp [hij']
}

theorem H_comm_X {n : ℕ} {i j : Fin n} (hij : i ≠ j) : (app (H i)) ≫ (app (X j)) ≡ (app (X j)) ≫ (app (H i)) := by {
  intro ψ
  dsimp [Qeval]
  unfold Qeval_gate
  simp
  exact (HX_comm ψ hij.symm).symm
}

theorem H_comm_H {n : ℕ} {i j : Fin n} (hij : i ≠ j) : (app (H i)) ≫ (app (H j)) ≡ (app (H j)) ≫ (app (H i)) := by {
  intro ψ
  dsimp [Qeval]
  unfold Qeval_gate
  simp
  exact H_comm ψ hij
}

theorem CZ_comm_CZ {n : ℕ} {i j : Fin n} (hij : i ≠ j) : (app (CZ i j)) ≡ (app (CZ j i)) := by {
  intro ψ
  dsimp [Qeval]
  funext bs
  unfold Qeval_gate app_CZ
  simp
  have hji : j ≠ i := by rw [ne_eq]; exact hij.symm
  cases hi : bs i <;> cases hj : bs j <;> simp [hji]; intros _; contradiction
}

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

theorem CNOT_rev {n : ℕ} {i j : Fin n} (hij : i ≠ j) : (app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H i) ≫ app (H j)) ≡ (app (CNOT j i)) := by {
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
  (app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i)) := by {
    apply seq_congr_right
    apply seq_congr_right
    apply seq_congr_right
    apply H_comm_H hij
  }
  have s2 :
  (app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i)) ≡
  (app (H i) ≫ app (CZ i j) ≫ app (H i)) := by {
    -- app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i) ≡ app (H i) ≫ app (CZ i j) ≫ app (H i)
    apply seq_congr_right
    intros _
    rw [← seq_assoc]
    rw [← seq_assoc]
    apply seq_congr_left
    intros _
    rw [seq_assoc]
    apply H_CNOT_H_eq_CZ hij
  }
  -- app (H i) ≫ app (H j) ≫ app (CNOT i j) ≫ app (H j) ≫ app (H i) ≡ app (CNOT j i)
  -- app (H i) ≫ app (CZ i j) ≫ app (H i) ≡ app (CNOT j i)
  have s3 :
  (app (H i) ≫ app (CZ i j) ≫ app (H i)) ≡
  (app (H i) ≫ app (CZ j i) ≫ app (H i)) := by {
    apply seq_congr_right
    apply seq_congr_left
    apply CZ_comm_CZ hij
  }
  -- app (H i) ≫ app (CZ j i) ≫ app (H i) ≡ app (CNOT j i)
  have s4 :
  (app (H i) ≫ app (CZ j i) ≫ app (H i)) ≡
  (app (CNOT j i)) := by {
    have hij' : j ≠ i := by rw [ne_eq]; exact hij.symm
    apply H_CZ_H_eq_CNOT hij'
  }
  exact equiv_trans s1 (equiv_trans s2 (equiv_trans s3 s4))
}

-- bell states

def gate_H_0 : QCircuit 2 := app (H (Fin.ofNat 2 0))
def gate_CNOT_0_1 : QCircuit 2 := app (CNOT (Fin.ofNat 2 0) (Fin.ofNat 2 1))
def bell_pre : QCircuit 2 := gate_H_0 ≫ gate_CNOT_0_1

lemma bell_prep_on_basis00 : 〚 bell_pre 〛 basis_00 = bell_plus_state := by {
  exact bell_state_from_H_CNOT
}

lemma bell_minus_from_prep_by_Z : 〚 bell_pre ≫ (app (Z (Fin.ofNat 2 1)) ) 〛 basis_00 = bell_minus_state := by {
  exact bell_minus_from_H_CNOT_Z
}

/-
Future Notes:
  - Introduce tactic for reducing circuits to simpler forms
  (use existing theorems for reduction and automation)
  - Introduce metaprogramming tactic for applying equivalence
  theorems based on the structure of the given circuit
-/
