import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumTactics

open QGate QCircuit

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
        unfold app_Uf_DJA app_X
        simp
        funext bs
        split_ifs with hc1 <;> simp [hc1]
      }
      {
        rename_i n
        unfold app_Uf_Simon
        rfl
      }
  }
  rw [h_linear ψ₂]
  use θ
}
