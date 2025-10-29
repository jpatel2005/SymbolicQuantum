import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval

open QGate QCircuit

def GlobalPhaseEq {n : ℕ}
  (ψ₁ ψ₂ : QState n) : Prop :=
  ∃ (c : ℂ), c ≠ 0 ∧ ψ₁ = c * ψ₂

infix:50 "≡ₚ " => GlobalPhaseEq

def parity (f : Qubit -> Qubit) : Qubit :=
  if f Qubit.zero = f Qubit.one then Qubit.zero else Qubit.one

inductive FCase | const0 | const1 | id | not
deriving DecidableEq, Repr

def classify (f : Qubit -> Qubit) : FCase :=
  match f Qubit.zero, f Qubit.one with
  | Qubit.zero, Qubit.zero => FCase.const0
  | Qubit.one,  Qubit.one  => FCase.const1
  | Qubit.zero, Qubit.one  => FCase.id
  | Qubit.one,  Qubit.zero => FCase.not

def phase_oracle (f : Qubit -> Qubit) : QCircuit 2 :=
  match classify f with
  | FCase.const0 => skip
  | FCase.const1 => app (X 1)
  | FCase.id     => app (CNOT 1 0)
  | FCase.not    => app (CNOT 1 0) ≫ app (X 1)

def deutsch : QCircuit 2 :=
  app (H 0) ≫
  app (H 1) ≫
  phase_oracle (fun x => x) ≫
  app (H 0)

def ket01 : QState 2 :=
  fun bs =>
    match bs 0, bs 1 with
    | Qubit.zero, Qubit.one => 1
    | _, _                  => 0

noncomputable def deutsch_post : QState 2 :=
  fun bs =>
    match bs 0, bs 1 with
    | Qubit.zero, Qubit.zero => 1 / (Real.sqrt 2)
    | Qubit.zero, Qubit.one  => -1 / (Real.sqrt 2)
    | _, _                   => 0

theorem Deutsch_correctness_const0 :
〚app (H 0) ≫
        app (H 1) ≫
          (match FCase.const0 with
            | FCase.const0 => skip
            | FCase.const1 => app (X 1)
            | FCase.id => app (CNOT 1 0)
            | FCase.not => app (CNOT 1 0) ≫ app (X 1)) ≫
            app (H 0)〛
    ket01≡ₚ
  deutsch_post := by {
    simp
    have h1 : 〚app (H (0:Fin 2)) ≫ app (H 1) ≫ skip ≫ app (H 0)〛 = 〚app (H 0) ≫ app (H 1) ≫ app (H 0)〛 := by {
      rfl
    }
    rw [h1]
    have h2 : app (H (0:Fin 2)) ≫ app (H 1) ≫ app (H 0) ≡ app (H 0) ≫ app (H 0) ≫ app (H 1) := by {
      intros _
      apply seq_congr_right
      apply H_comm_H
      simp
    }
    rw [h2]
    have h3 : app (H (0:Fin 2)) ≫ app (H 0) ≫ app (H 1) ≡ skip ≫ app (H 1) := by {
      intros _
      rw [← seq_assoc]
      apply seq_congr_left
      apply H_H_equiv_skip
    }
    rw [h3]
    have h4 : skip ≫ app (H (1:Fin 2)) ≡ app (H 1) := by {
      apply seq_skip_left
    }
    rw [h4]
    use 1
    repeat unfold Qeval
    unfold Qeval_gate
    unfold ket01
    unfold deutsch_post
    unfold app_H
    simp
    funext bs
    cases hb0: bs 0 <;> cases hb1: bs 1 <;> simp
    try any_goals {
      field_simp
      ring_nf
      conv_rhs=>
        arg 2
        change ((1 : ℂ) * (fun (bs : BitString 2) ↦
            ((match bs 0, bs 1 with
            | Qubit.zero, Qubit.zero => ((√2)⁻¹ : ℂ)
            | Qubit.zero, Qubit.one => -((√2)⁻¹ : ℂ)
            | _, _ => (0 : ℂ)) : ℂ))
        bs)
      simp [hb0,hb1]
    }
    all_goals
    {
      field_simp
      ring_nf
      conv_rhs=>
        change ((1 : ℂ) * (fun (bs : BitString 2) ↦
            ((match bs 0, bs 1 with
            | Qubit.zero, Qubit.zero => ((√2)⁻¹ : ℂ)
            | Qubit.zero, Qubit.one => -((√2)⁻¹ : ℂ)
            | _, _ => (0 : ℂ)) : ℂ))
        bs)
      simp [hb0,hb1]
    }
}

theorem Deutsch_correctness_const1  :
〚app (H 0) ≫
        app (H 1) ≫
          (match FCase.const1 with
            | FCase.const0 => skip
            | FCase.const1 => app (X 1)
            | FCase.id => app (CNOT 1 0)
            | FCase.not => app (CNOT 1 0) ≫ app (X 1)) ≫
            app (H 0)〛
    ket01≡ₚ
  deutsch_post := by {
    simp
    have h1 : app (H (0:Fin 2)) ≫ app (H 1) ≫ app (X 1) ≫ app (H 0) ≡ app (H 1) ≫ app (H 0) ≫ app (X 1) ≫ app (H 0) := by {
      intros _
      rw [← seq_assoc]
      rw [← seq_assoc]
      rw [← seq_assoc]
      rw [← seq_assoc]
      apply seq_congr_left
      apply seq_congr_left
      apply H_comm_H
      simp
    }
    rw [h1]
    have h2 : app (H (1:Fin 2)) ≫ app (H 0) ≫ app (X 1) ≫ app (H 0) ≡ app (H 1) ≫ app (X 1) ≫ app (H 0) ≫ app (H 0) := by {
      apply seq_congr_right
      intros _
      rw [← seq_assoc]
      rw [← seq_assoc]
      apply seq_congr_left
      apply H_comm_X
      simp
    }
    rw [h2]
    have h3 : app (H (1:Fin 2)) ≫ app (X 1) ≫ app (H 0) ≫ app (H 0) ≡ app (H 1) ≫ app (X 1) ≫ skip := by {
      intros _
      rw [← seq_assoc]
      apply seq_congr_right
      apply H_H_equiv_skip
    }
    rw [h3]
    use -1
    simp
    repeat unfold Qeval
    unfold Qeval_gate
    unfold ket01
    unfold deutsch_post
    unfold app_X app_H
    simp
    ring_nf
    funext bs
    conv_rhs=>
      change ((-1 : ℂ) * (fun (bs : BitString 2) ↦
          ((match bs 0, bs 1 with
          | Qubit.zero, Qubit.zero => ((√2)⁻¹ : ℂ)
          | Qubit.zero, Qubit.one => -((√2)⁻¹ : ℂ)
          | _, _ => (0 : ℂ)) : ℂ))
      bs)
    cases hb0: bs 0 <;> (cases hb1: bs 1 <;> (simp [hb0,hb1]))
}

theorem Deutsch_correctness_id :
〚app (H 0) ≫
        app (H 1) ≫
          (match FCase.id with
            | FCase.const0 => skip
            | FCase.const1 => app (X 1)
            | FCase.id => app (CNOT 1 0)
            | FCase.not => app (CNOT 1 0) ≫ app (X 1)) ≫
            app (H 0)〛
    ket01≡ₚ
  deutsch_post := by {
  simp
  have h1 : app (H (0:Fin 2)) ≫ app (H 1) ≫ app (CNOT 1 0) ≫ app (H 0) ≡ app (H 1) ≫ app (H 0) ≫ app (CNOT 1 0) ≫ app (H 0) := by {
    intros _
    rw [← seq_assoc]
    rw [← seq_assoc]
    rw [← seq_assoc]
    rw [← seq_assoc]
    apply seq_congr_left
    apply seq_congr_left
    apply H_comm_H
    simp
  }
  rw [h1]
  have h2 : app (H (1:Fin 2)) ≫ app (H 0) ≫ app (CNOT 1 0) ≫ app (H 0) ≡ app (H 1) ≫ app (CZ 1 0) := by {
    apply seq_congr_right
    apply H_CNOT_H_eq_CZ
    simp
  }
  rw [h2]
  use 1
  simp
  repeat unfold Qeval
  unfold Qeval_gate
  unfold ket01
  unfold deutsch_post
  unfold app_CZ app_H
  simp
  ring_nf
  funext bs
  conv_rhs=>
    change ((1 : ℂ) * (fun (bs : BitString 2) ↦
        ((match bs 0, bs 1 with
        | Qubit.zero, Qubit.zero => ((√2)⁻¹ : ℂ)
        | Qubit.zero, Qubit.one => -((√2)⁻¹ : ℂ)
        | _, _ => (0 : ℂ)) : ℂ))
    bs)
  simp
  cases bs 0 <;> (cases bs 1 <;> (simp))
}

theorem Deutsch_correctness_not :
〚app (H 0) ≫
        app (H 1) ≫
          (match FCase.not with
            | FCase.const0 => skip
            | FCase.const1 => app (X 1)
            | FCase.id => app (CNOT 1 0)
            | FCase.not => app (CNOT 1 0) ≫ app (X 1)) ≫
            app (H 0)〛
    ket01≡ₚ
  deutsch_post := by {
  simp
  have h1 : app (H (0:Fin 2)) ≫ app (H 1) ≫ (app (CNOT 1 0) ≫ app (X 1)) ≫ app (H 0) ≡
            app (H 1) ≫ app (H 0) ≫ (app (CNOT 1 0) ≫ app (X 1)) ≫ app (H 0) := by {
    intros _
    rw [← seq_assoc]
    rw [← seq_assoc]
    rw [← seq_assoc]
    rw [← seq_assoc]
    apply seq_congr_left
    apply seq_congr_left
    apply H_comm_H
    simp
  }
  rw [h1]
  have h2 : app (H (1:Fin 2)) ≫ app (H 0) ≫ (app (CNOT 1 0) ≫ app (X 1)) ≫ app (H 0) ≡
            app (H 1) ≫ app (H 0) ≫ app (CNOT 1 0) ≫ app (H 0) ≫ app (X 1) := by {
    apply seq_congr_right
    apply seq_congr_right
    intros _
    rw [seq_assoc]
    apply seq_congr_right
    symm
    apply H_comm_X
    simp
  }
  rw [h2]
  have h3 : app (H (1:Fin 2)) ≫ app (H 0) ≫ app (CNOT 1 0) ≫ app (H 0) ≫ app (X 1) ≡
            app (H 1) ≫ app (CZ 1 0) ≫ app (X 1) := by {
    apply seq_congr_right
    intros _
    rw [← seq_assoc]
    rw [← seq_assoc]
    apply seq_congr_left
    intros _
    rw [seq_assoc]
    apply H_CNOT_H_eq_CZ
    simp
  }
  rw [h3]
  use -1
  simp
  repeat unfold Qeval
  unfold Qeval_gate
  unfold ket01
  unfold deutsch_post
  unfold app_CZ app_H app_X
  simp
  ring_nf
  funext bs
  conv_rhs=>
    change ((-1 : ℂ) * (fun (bs : BitString 2) ↦
        ((match bs 0, bs 1 with
        | Qubit.zero, Qubit.zero => ((√2)⁻¹ : ℂ)
        | Qubit.zero, Qubit.one => -((√2)⁻¹ : ℂ)
        | _, _ => (0 : ℂ)) : ℂ))
    bs)
  simp
  cases bs 0 <;> cases bs 1 <;> simp
}

theorem Deutsch_correctness : (Qeval deutsch ket01) ≡ₚ deutsch_post := by {
  unfold deutsch
  unfold phase_oracle
  cases h : classify (fun x => x)
  { exact Deutsch_correctness_const0 }
  { exact Deutsch_correctness_const1 }
  { exact Deutsch_correctness_id }
  { exact Deutsch_correctness_not }
}
