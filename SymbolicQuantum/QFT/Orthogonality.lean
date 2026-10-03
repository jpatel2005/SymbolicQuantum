import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumDefs

/-
  Numeric view of a bitstring, and the orthogonality sum the QFT analysis rests on.
-/

def qubitEquivFin2 : Qubit ≃ Fin 2 where
  toFun q := match q with | Qubit.zero => 0 | Qubit.one => 1
  invFun i := if i = 0 then Qubit.zero else Qubit.one
  left_inv q := by cases q <;> rfl
  right_inv i := by fin_cases i <;> rfl

-- the numeric view: a bitstring is a residue mod 2^n
def bitStringEquivFin {n : ℕ} : BitString n ≃ Fin (2 ^ n) :=
  (Equiv.piCongrRight fun _ : Fin n => qubitEquivFin2).trans finFunctionFinEquiv

def BitString.toNat {n : ℕ} (bs : BitString n) : ℕ := (bitStringEquivFin bs).val

noncomputable def omegaPow (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma omegaPow_primitive {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (omegaPow N) N :=
  Complex.isPrimitiveRoot_exp N hN

/- The orthogonality sum. -/

theorem sum_omegaPow_mul {N : ℕ} (hN : N ≠ 0) (d : ℕ) :
    ∑ x : Fin N, (omegaPow N) ^ (x.val * d) = if N ∣ d then (N : ℂ) else 0 := by
  have hprim := omegaPow_primitive hN
  have hrw : ∀ x : Fin N, (omegaPow N) ^ (x.val * d) = ((omegaPow N) ^ d) ^ x.val := by
    intro x
    rw [mul_comm, pow_mul]
  simp only [hrw]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((omegaPow N) ^ d) ^ i) N]
  by_cases hdvd : N ∣ d
  · rw [if_pos hdvd, (hprim.pow_eq_one_iff_dvd d).mpr hdvd]
    simp
  · rw [if_neg hdvd]
    have hne : (omegaPow N) ^ d ≠ 1 := fun h => hdvd ((hprim.pow_eq_one_iff_dvd d).mp h)
    rw [geom_sum_eq hne]
    have hN1 : ((omegaPow N) ^ d) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [hN1, sub_self, zero_div]

/- The same sum in the framework's own idiom, over bitstrings. -/

theorem sum_bitString_omegaPow_mul {n : ℕ} (d : ℕ) :
    ∑ x : BitString n, (omegaPow (2 ^ n)) ^ (x.toNat * d)
      = if 2 ^ n ∣ d then ((2 ^ n : ℕ) : ℂ) else 0 := by
  rw [← sum_omegaPow_mul (N := 2 ^ n) (Nat.two_pow_pos n).ne' d]
  exact Fintype.sum_equiv bitStringEquivFin _ _ (fun _ => rfl)

/- Integer-exponent form, which is what a difference of two indices needs. -/

theorem sum_omegaPow_zpow {N : ℕ} (hN : N ≠ 0) (d : ℤ) :
    ∑ x : Fin N, (omegaPow N) ^ ((x.val : ℤ) * d) = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  have hprim := omegaPow_primitive hN
  have hrw : ∀ x : Fin N, (omegaPow N) ^ ((x.val : ℤ) * d) = ((omegaPow N) ^ d) ^ x.val := by
    intro x
    rw [mul_comm, zpow_mul, zpow_natCast]
  simp only [hrw]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((omegaPow N) ^ d) ^ i) N]
  by_cases hdvd : (N : ℤ) ∣ d
  · rw [if_pos hdvd, (hprim.zpow_eq_one_iff_dvd d).mpr hdvd]
    simp
  · rw [if_neg hdvd]
    have hne : (omegaPow N) ^ d ≠ 1 := fun h => hdvd ((hprim.zpow_eq_one_iff_dvd d).mp h)
    rw [geom_sum_eq hne]
    have hN1 : ((omegaPow N) ^ d) ^ N = 1 := by
      rw [← zpow_natCast ((omegaPow N) ^ d) N, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hprim.pow_eq_one, one_zpow]
    rw [hN1, sub_self, zero_div]

/- The numeric view is injective and bounded, so divisibility collapses to equality. -/

lemma BitString.toNat_lt {n : ℕ} (bs : BitString n) : bs.toNat < 2 ^ n :=
  (bitStringEquivFin bs).isLt

lemma BitString.toNat_injective {n : ℕ} : Function.Injective (BitString.toNat (n := n)) :=
  fun _ _ h => bitStringEquivFin.injective (Fin.ext h)

/- QFT column orthogonality, stated over bitstrings. -/

theorem sum_bitString_omegaPow_sub {n : ℕ} (j k : BitString n) :
    ∑ x : BitString n, (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * ((j.toNat : ℤ) - (k.toNat : ℤ)))
      = if j = k then ((2 ^ n : ℕ) : ℂ) else 0 := by
  have htrans :
      ∑ x : BitString n, (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * ((j.toNat : ℤ) - (k.toNat : ℤ)))
        = ∑ x : Fin (2 ^ n), (omegaPow (2 ^ n)) ^ ((x.val : ℤ) * ((j.toNat : ℤ) - (k.toNat : ℤ))) :=
    Fintype.sum_equiv bitStringEquivFin _ _ (fun _ => rfl)
  rw [htrans, sum_omegaPow_zpow (Nat.two_pow_pos n).ne']
  congr 1
  apply propext
  constructor
  · intro hdvd
    have hj := BitString.toNat_lt j
    have hk := BitString.toNat_lt k
    have habs : |(j.toNat : ℤ) - (k.toNat : ℤ)| < ((2 ^ n : ℕ) : ℤ) := by
      rw [abs_lt]; omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact BitString.toNat_injective (by omega)
  · rintro rfl
    simp

/- The QFT as an amplitude transform, in the same style as the other gates. -/

lemma omegaPow_ne_zero {N : ℕ} : omegaPow N ≠ 0 := Complex.exp_ne_zero _

noncomputable def app_QFT {n : ℕ} (ψ : QState n) : QState n :=
  fun bs => (1 / Real.sqrt (2 ^ n) : ℂ) *
    ∑ x : BitString n, (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * (bs.toNat : ℤ)) * ψ x

noncomputable def app_QFT_inv {n : ℕ} (ψ : QState n) : QState n :=
  fun bs => (1 / Real.sqrt (2 ^ n) : ℂ) *
    ∑ x : BitString n, (omegaPow (2 ^ n)) ^ (-(x.toNat : ℤ) * (bs.toNat : ℤ)) * ψ x

lemma inv_sqrt_two_pow_sq (n : ℕ) :
    (1 / Real.sqrt (2 ^ n) : ℂ) * ((1 / Real.sqrt (2 ^ n) : ℂ) * ((2 ^ n : ℕ) : ℂ)) = 1 := by
  have h : (0:ℝ) < 2 ^ n := by positivity
  have hs : (Real.sqrt ((2:ℝ) ^ n) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr h).ne'
  field_simp
  rw [← Complex.ofReal_pow, Real.sq_sqrt h.le]
  push_cast
  ring

/- The round trip. This is the lemma the orthogonality sum exists to serve. -/

theorem app_QFT_inv_app_QFT {n : ℕ} (ψ : QState n) : app_QFT_inv (app_QFT ψ) = ψ := by
  funext b
  have hexp : ∀ x y : BitString n,
      (omegaPow (2 ^ n)) ^ (-(y.toNat : ℤ) * (b.toNat : ℤ)) *
        ((omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * (y.toNat : ℤ)) * ψ x)
      = (omegaPow (2 ^ n)) ^ ((y.toNat : ℤ) * ((x.toNat : ℤ) - (b.toNat : ℤ))) * ψ x := by
    intro x y
    rw [← mul_assoc, ← zpow_add₀ omegaPow_ne_zero]
    congr 2
    ring
  have key : (∑ y : BitString n, (omegaPow (2 ^ n)) ^ (-(y.toNat : ℤ) * (b.toNat : ℤ)) *
        ∑ x : BitString n, (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * (y.toNat : ℤ)) * ψ x)
      = ((2 ^ n : ℕ) : ℂ) * ψ b := by
    simp_rw [Finset.mul_sum, hexp]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_bitString_omegaPow_sub]
    simp [ite_mul]
  simp only [app_QFT, app_QFT_inv]
  have hpull : ∀ y : BitString n,
      (omegaPow (2 ^ n)) ^ (-(y.toNat : ℤ) * (b.toNat : ℤ)) *
        ((1 / Real.sqrt (2 ^ n) : ℂ) *
          ∑ x : BitString n, (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * (y.toNat : ℤ)) * ψ x)
      = (1 / Real.sqrt (2 ^ n) : ℂ) *
          ((omegaPow (2 ^ n)) ^ (-(y.toNat : ℤ) * (b.toNat : ℤ)) *
            ∑ x : BitString n, (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * (y.toNat : ℤ)) * ψ x) := by
    intro y
    ring
  simp_rw [hpull]
  rw [← Finset.mul_sum, key]
  calc (1 / Real.sqrt (2 ^ n) : ℂ) *
        ((1 / Real.sqrt (2 ^ n) : ℂ) * (((2 ^ n : ℕ) : ℂ) * ψ b))
      = ((1 / Real.sqrt (2 ^ n) : ℂ) *
          ((1 / Real.sqrt (2 ^ n) : ℂ) * ((2 ^ n : ℕ) : ℂ))) * ψ b := by ring
    _ = 1 * ψ b := by rw [inv_sqrt_two_pow_sq]
    _ = ψ b := one_mul _
