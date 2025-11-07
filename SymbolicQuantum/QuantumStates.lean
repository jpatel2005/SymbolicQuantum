import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

inductive Qubit
| zero : Qubit
| one  : Qubit
deriving DecidableEq, Inhabited, Repr

-- represent a bitstring as a function from indices to qubits
def BitString (n : Nat) := Fin n → Qubit

instance {n : ℕ} : DecidableEq (BitString n) := inferInstanceAs (DecidableEq (Fin n → Qubit))

def QState (n : ℕ) : Type := BitString n → ℂ

-- Define negation and scalar multiplication for QState

instance {n : ℕ} : Neg (QState n) where
  neg ψ := fun bs => - (ψ bs)

instance {n : ℕ} : HMul ℂ (QState n) (QState n) where
  hMul c ψ := fun bs => c * ψ bs

def app_X {n : ℕ} (ψ : QState n) (k : Fin n) : QState n :=
  fun bs =>
    let flipped :=
      fun j =>
        if j = k then
          match bs j with
          | Qubit.zero => Qubit.one
          | Qubit.one  => Qubit.zero
        else bs j
    ψ flipped

-- Consider updating this definition for easier proofs

def app_Y {n : ℕ} (ψ : QState n) (k : Fin n) : QState n :=
  fun bs =>
    let flipped := fun j =>
      if j = k then
        match bs j with
        | Qubit.zero => Qubit.one
        | Qubit.one  => Qubit.zero
      else bs j
    let phase := match bs k with
      | Qubit.zero => Complex.I
      | Qubit.one  => -Complex.I
    phase * ψ flipped

def app_Z {n : ℕ} (ψ : QState n) (k : Fin n) : QState n :=
  fun bs =>
    let phase := match bs k with
      | Qubit.zero => 1
      | Qubit.one  => -1
    phase * ψ bs

def app_CNOT {n : ℕ} (ψ : QState n) (control target : Fin n) : QState n :=
  fun bs =>
    if control = target then ψ bs
    else
      let flipped :=
        fun j =>
          if j = target then
            match bs control with
            | Qubit.zero => bs target
            | Qubit.one  =>
              match bs target with
              | Qubit.zero => Qubit.one
              | Qubit.one  => Qubit.zero
          else bs j
      ψ flipped

noncomputable def app_H {n : ℕ} (ψ : QState n) (k : Fin n) : QState n :=
  fun bs =>
    let zero_bs i := if i = k then Qubit.zero else bs i
    let one_bs i := if i = k then Qubit.one else bs i
    (match bs k with
    | Qubit.zero => (ψ zero_bs + ψ one_bs)
    | Qubit.one  => (ψ zero_bs - ψ one_bs)) * (1 / Real.sqrt 2)

def app_CZ {n : ℕ} (ψ : QState n) (control target : Fin n) : QState n :=
  fun bs =>
    if control = target then ψ bs
    else
      match bs control with
      | Qubit.zero => ψ bs
      | Qubit.one  =>
        match bs target with
        | Qubit.zero => ψ bs
        | Qubit.one  => - (ψ bs)

def app_Uf {n : ℕ} (ψ : QState n) (f : BitString n -> Bool) (k : Fin n) : QState n :=
  fun bs =>
    if f bs then
      app_X ψ k bs
    else
      ψ bs

lemma invSqrt2Square : ((√2 : ℂ) ^ 2)⁻¹ = 1 / 2 := by {
  rw [pow_two]
  rw [← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (by simp)]
  norm_num
}

lemma sqrt2_mul_sqrt2 : (√2 : ℂ) * (√2 : ℂ) = 2 := by {
  rw [← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (by simp)]
  norm_num
}

theorem X_involutive {n : ℕ} (ψ : QState n) (k : Fin n) : app_X (app_X ψ k) k = ψ := by {
  funext bs
  dsimp [app_X]
  apply congr_arg ψ
  funext j
  by_cases hj : j = k
  · simp [hj]
    cases (bs k) <;> simp
  · simp [hj]
}

theorem Y_involutive {n : ℕ} (ψ : QState n) (k : Fin n) : app_Y (app_Y ψ k) k = ψ := by {
  funext bs
  dsimp [app_Y]
  cases (bs k) <;> (
    simp
    ring_nf
    norm_num
    apply congr_arg ψ
    funext j
    by_cases hj : j = k
    · simp [hj]
      cases (bs k) <;> simp
    · simp [hj]
  )
}

theorem Z_involutive {n : ℕ} (ψ : QState n) (k : Fin n) : app_Z (app_Z ψ k) k = ψ := by {
  funext bs
  dsimp [app_Z]
  cases (bs k) <;> simp
}

theorem CZ_involutive {n : ℕ} (ψ : QState n) (i j : Fin n) (h : i ≠ j) : app_CZ (app_CZ ψ i j) i j = ψ := by {
  funext bs
  dsimp [app_CZ]
  by_cases hij : i = j
  · exfalso
    exact h hij
  · simp [hij]
    cases (bs i) <;> (cases (bs j) <;> simp)
}

-- Anti-commutation relations

theorem XY_anticomm {n : ℕ} (ψ : QState n) (k : Fin n) : app_Y (app_X ψ k) k = -(app_X (app_Y ψ k) k) := by {
  funext bs
  unfold app_X app_Y
  simp_all
  rw [Pi.neg_apply]
  ring_nf
  cases (bs k) <;> (simp;rw[mul_comm])
}

theorem XZ_anticomm {n : ℕ} (ψ : QState n) (k : Fin n) : app_Z (app_X ψ k) k = -(app_X (app_Z ψ k) k) := by {
  funext bs
  unfold app_X app_Z
  simp_all
  rw [Pi.neg_apply]
  ring_nf
  cases (bs k) <;> simp
}

theorem YZ_anticomm {n : ℕ} (ψ : QState n) (k : Fin n) : app_Z (app_Y ψ k) k = -(app_Y (app_Z ψ k) k) := by {
  funext bs
  unfold app_Y app_Z
  simp_all
  rw [Pi.neg_apply]
  ring_nf
  cases (bs k) <;> simp
}

-- Multiplication rules

theorem XY_iZ {n : ℕ} (ψ : QState n) (k : Fin n) : (app_Y (app_X ψ k) k) = Complex.I * (app_Z ψ k) := by {
  funext bs
  unfold app_X app_Y app_Z
  simp
  cases hk: (bs k) <;> simp_all
  {
    congr 1
    simp [hk]
    apply congr_arg ψ
    funext j
    by_cases hj : j = k <;> simp [hj, hk]
  }
  {
    rw [← mul_neg]
    congr 1
    simp [hk]
    apply congr_arg ψ
    funext j
    by_cases hj : j = k <;> simp [hj, hk]
  }
}

theorem YZ_iX {n : ℕ} (ψ : QState n) (k : Fin n) : (app_Z (app_Y ψ k) k) = Complex.I * (app_X ψ k) := by {
  funext bs
  unfold app_X app_Y app_Z
  simp
  cases hk: (bs k) <;> (
    simp_all
    congr 1
    simp [hk]
  )
}

-- tricky
theorem ZX_iY {n : ℕ} (ψ : QState n) (k : Fin n) : (app_X (app_Z ψ k) k) = Complex.I * (app_Y ψ k) := by {
  sorry
}

theorem CNOT_involutive {n : ℕ} (ψ : QState n) (i j : Fin n) (h : i ≠ j) : app_CNOT (app_CNOT ψ i j) i j = ψ := by {
  funext bs
  unfold app_CNOT
  simp_all
  apply congr_arg ψ
  funext k
  by_cases hkj : k = j
  · simp [hkj]
    cases (bs i) <;> simp
    cases (bs j) <;> simp
  · simp [hkj]
}

theorem CNOT_bridge {n : ℕ} (ψ : QState n) (i j k : Fin n) (h1 : i ≠ j) (h2 : j ≠ k) (h3 : i ≠ k) :
app_CNOT (app_CNOT (app_CNOT (app_CNOT ψ i j) j k) i j) j k = app_CNOT ψ i k := by {
  funext bs
  unfold app_CNOT
  simp_all
  apply congr_arg ψ
  funext p
  by_cases hpj : p = j
  · simp [h2, hpj]
    cases (bs i) <;> simp
    cases (bs j) <;> simp
  · simp [hpj]
    by_cases hpk : p = k
    · simp [hpk]
      cases (bs i) <;> simp
      {
        cases (bs j) <;> simp
        {
          intros h
          exfalso
          apply h2
          exact h.symm
        }
        {
          have : k ≠ j := by {
            intro h
            apply h2
            rw [h]
          }
          simp [this]
          cases (bs k) <;> simp
        }
      }
      {
        cases (bs j) <;> simp
        {
          have : k ≠ j := by {
            intro h
            apply h2
            rw [h]
          }
          simp [this]
        }
        {
          intros h
          exfalso
          apply h2
          exact h.symm
        }
      }
    · simp [hpk]
}

theorem H_involutive {n : ℕ} (ψ : QState n) (k : Fin n) : app_H (app_H ψ k) k = ψ := by {
  funext bs
  unfold app_H
  simp_all
  ring_nf
  cases hk : (bs k) <;> simp
  all_goals (
    field_simp
    rw [pow_two, sqrt2_mul_sqrt2, mul_comm 2]
    congr
    funext j
    by_cases hj : j = k <;> simp [hj, hk]
  )
}

-- Bell State Preparation using H and CNOT

def basis_00 : QState 2 :=
  fun bs =>
    match bs 0, bs 1 with
    | Qubit.zero, Qubit.zero => 1
    | _, _ => 0

noncomputable def bell_plus_state : QState 2 :=
  fun bs =>
    match bs 0, bs 1 with
    | Qubit.zero, Qubit.zero => 1 / Real.sqrt 2
    | Qubit.one,  Qubit.one  => 1 / Real.sqrt 2
    | _, _ => 0

noncomputable def bell_minus_state : QState 2 :=
  fun bs =>
    match bs 0, bs 1 with
    | Qubit.zero, Qubit.zero => 1 / Real.sqrt 2
    | Qubit.one,  Qubit.one  => -1 / Real.sqrt 2
    | _, _ => 0

theorem bell_state_from_H_CNOT : app_CNOT (app_H basis_00 0) 0 1 = bell_plus_state := by {
  funext bs
  unfold app_CNOT app_H basis_00 bell_plus_state
  simp_all
  split
  next x heq =>
    simp [heq]
    cases (bs 1) <;> simp
  next x heq =>
    simp [heq]
    cases (bs 1) <;> simp
}

theorem bell_minus_from_H_CNOT_Z :
  app_Z (app_CNOT (app_H basis_00 0) 0 1) 1 = bell_minus_state := by {
  funext bs
  unfold app_CNOT app_H app_Z basis_00 bell_minus_state
  simp_all
  split
  next x heq =>
    simp [heq]
    cases (bs 0) <;> simp
  next x heq =>
    simp [heq]
    cases (bs 0) <;> simp
    ring_nf
}

theorem HXH_Z {n : ℕ} (ψ : QState n) (k : Fin n) : app_H (app_X (app_H ψ k) k) k = app_Z ψ k := by {
  funext bs
  unfold app_H app_X app_Z
  simp_all
  ring_nf
  cases hk : (bs k) <;> simp
  all_goals (
    field_simp
    rw [pow_two, sqrt2_mul_sqrt2, mul_comm 2]
    congr
    funext j
    by_cases hj : j = k <;> simp [hj, hk]
  )
}

theorem HZH_X {n : ℕ} (ψ : QState n) (k : Fin n) : app_H (app_Z (app_H ψ k) k) k = app_X ψ k := by {
  funext bs
  unfold app_H app_X app_Z
  simp_all
  ring_nf
  cases hk : (bs k) <;> simp
  all_goals (
    field_simp
    rw [pow_two, sqrt2_mul_sqrt2, mul_comm 2]
  )
}

theorem H_CNOT_H_CZ {n : ℕ} (ψ : QState n) {i j : Fin n} (hij : i ≠ j) :
(app_H (app_CNOT (app_H ψ j) i j) j) = (app_CZ ψ i j) := by {
  funext bs
  unfold app_H app_CNOT app_CZ
  simp [hij]
  ring_nf
  cases hi : bs i <;> (cases hj : bs j <;> (
    ring_nf
    simp_all[invSqrt2Square]
    ring_nf
    try rw [neg_inj]
    apply congr_arg ψ
    funext k
    by_cases hk : k = j <;> simp [hk, hj]
  ))
}

theorem H_CZ_H_CNOT {n : ℕ} (ψ : QState n) {i j : Fin n} (hij : i ≠ j) :
(app_H (app_CZ (app_H ψ j) i j) j) = (app_CNOT ψ i j) := by {
  funext bs
  unfold app_H app_CNOT app_CZ
  simp [hij]
  ring_nf
  cases hi : bs i <;> (cases hj : bs j <;> (
    ring_nf
    simp_all[invSqrt2Square]
    ring_nf
    try rw [neg_inj]
  ))
}

theorem CZ_comm {n : ℕ} (ψ : QState n) {i j : Fin n} (hij : i ≠ j) : (app_CZ ψ i j) = (app_CZ ψ j i) := by {
  funext bs
  unfold app_CZ
  have hij' : j ≠ i := by rw [ne_eq]; exact hij.symm
  simp [hij,hij']
  cases bs i <;> simp
  cases bs j <;> simp
}

theorem H_comm {n : ℕ} (ψ : QState n) {i j : Fin n} (hij : i ≠ j) : (app_H (app_H ψ i) j) = (app_H (app_H ψ j) i) := by {
  funext bs
  unfold app_H
  have hij' : j ≠ i := by rw [ne_eq]; exact hij.symm
  simp_all
  ring_nf
  cases hi : (bs i) <;> (cases hj : (bs j) <;> simp)
  all_goals {
    field_simp
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    congr
    all_goals {
      funext k
      by_cases hk : k = i <;> simp [hk, hij]
    }
  }
}

theorem HX_comm {n : ℕ} (ψ : QState n) {i j : Fin n} (hij : i ≠ j) : (app_H (app_X ψ i) j) = (app_X (app_H ψ j) i) := by {
  funext bs
  unfold app_H app_X
  have hij' : j ≠ i := by rw [ne_eq]; exact hij.symm
  simp_all
  ring_nf
  cases hi : (bs i) <;> (cases hj : (bs j) <;> simp)
  all_goals {
    field_simp
    simp [sub_eq_add_neg, add_comm]
    congr
    all_goals {
      funext k
      by_cases hk : k = i <;> simp [hk, hij]
    }
  }
}
