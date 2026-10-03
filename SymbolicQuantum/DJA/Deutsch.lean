import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumTactics
import SymbolicQuantum.GlobalPhase

open QGate QCircuit

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
  | FCase.id     => app (CNOT 0 1)
  | FCase.not    => app (CNOT 0 1) ≫ app (X 1)

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

noncomputable def deutsch_post_const : QState 2 :=
  fun bs =>
    match bs 0, bs 1 with
    | Qubit.zero, Qubit.zero => 1 / (Real.sqrt 2)
    | Qubit.zero, Qubit.one  => -1 / (Real.sqrt 2)
    | _, _                   => 0

noncomputable def deutsch_post_balanced : QState 2 :=
  fun bs =>
    match bs 0, bs 1 with
    | Qubit.one, Qubit.zero => 1 / (Real.sqrt 2)
    | Qubit.one, Qubit.one  => -1 / (Real.sqrt 2)
    | _, _                  => 0

theorem Deutsch_correctness_const0 :
〚app (H 0) ≫ app (H 1) ≫ skip ≫ app (H 0)〛 ket01 ≡ₚ deutsch_post_const := by {
  have h1 : 〚app (H (0:Fin 2)) ≫ app (H 1) ≫ skip ≫ app (H 0)〛 = 〚app (H 0) ≫ app (H 1) ≫ app (H 0)〛 := by {
    rfl
  }
  rw [h1]
  have h2 : app (H (0:Fin 2)) ≫ app (H 1) ≫ app (H 0) ≡ app (H 0) ≫ app (H 0) ≫ app (H 1) := by {
    qseq (H_comm_H (by simp))
  }
  rw [h2]
  have h3 : app (H (0:Fin 2)) ≫ app (H 0) ≫ app (H 1) ≡ skip ≫ app (H 1) := by {
    qseq (H_H_equiv_skip)
  }
  rw [h3]
  have h4 : skip ≫ app (H (1:Fin 2)) ≡ app (H 1) := by {
    qseq ()
  }
  rw [h4]
  use 1
  repeat unfold Qeval
  unfold Qeval_gate
  unfold ket01
  unfold deutsch_post_const
  unfold app_H
  simp
  ring_nf
  funext bs
  cases hb0: bs 0 <;> cases hb1: bs 1 <;> simp [hb0,hb1]
}

theorem Deutsch_correctness_const1 :
〚app (H 0) ≫ app (H 1) ≫ app (X 1) ≫ app (H 0)〛 ket01 ≡ₚ deutsch_post_const := by {
  have h1 : app (H (0:Fin 2)) ≫ app (H 1) ≫ app (X 1) ≫ app (H 0) ≡ app (H 1) ≫ app (H 0) ≫ app (X 1) ≫ app (H 0) := by {
    qseq (H_comm_H (by simp))
  }
  rw [h1]
  have h2 : app (H (1:Fin 2)) ≫ app (H 0) ≫ app (X 1) ≫ app (H 0) ≡ app (H 1) ≫ app (X 1) ≫ app (H 0) ≫ app (H 0) := by {
    qseq (H_comm_X (by simp))
  }
  rw [h2]
  have h3 : app (H (1:Fin 2)) ≫ app (X 1) ≫ app (H 0) ≫ app (H 0) ≡ app (H 1) ≫ app (X 1) ≫ skip := by {
    qseq H_H_equiv_skip
  }
  rw [h3]
  use -1
  repeat unfold Qeval
  unfold Qeval_gate
  unfold ket01
  unfold deutsch_post_const
  unfold app_X app_H
  simp
  ring_nf
  funext bs
  cases hb0: bs 0 <;> (cases hb1: bs 1 <;> simp [hb0,hb1])
}

theorem Deutsch_correctness_id :
〚app (H 0) ≫ app (H 1) ≫ app (CNOT 0 1) ≫ app (H 0)〛 ket01 ≡ₚ deutsch_post_balanced := by {
  use 1
  repeat unfold Qeval
  unfold Qeval_gate
  unfold ket01
  unfold deutsch_post_balanced
  unfold app_CNOT app_H
  simp
  ring_nf
  funext bs
  have hs : ((√2 : ℂ))⁻¹ * ((√2 : ℂ))⁻¹ = 1 / 2 := by {
    rw [← mul_inv, sqrt2_mul_sqrt2]
    norm_num
  }
  cases hb0: bs 0 <;> (cases hb1: bs 1 <;> simp [hb0,hb1,hs] <;> norm_num)
}

theorem Deutsch_correctness_not :
〚app (H 0) ≫ app (H 1) ≫ (app (CNOT 0 1) ≫ app (X 1)) ≫ app (H 0)〛 ket01 ≡ₚ deutsch_post_balanced := by {
  use -1
  repeat unfold Qeval
  unfold Qeval_gate
  unfold ket01
  unfold deutsch_post_balanced
  unfold app_CNOT app_X app_H
  simp
  ring_nf
  funext bs
  have hs : ((√2 : ℂ))⁻¹ * ((√2 : ℂ))⁻¹ = 1 / 2 := by {
    rw [← mul_inv, sqrt2_mul_sqrt2]
    norm_num
  }
  cases hb0: bs 0 <;> (cases hb1: bs 1 <;> simp [hb0,hb1,hs] <;> norm_num)
}

theorem Deutsch_correctness : (Qeval deutsch ket01) ≡ₚ deutsch_post_balanced := by {
  unfold deutsch
  unfold phase_oracle
  exact Deutsch_correctness_id
}
