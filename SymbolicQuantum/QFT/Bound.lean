import SymbolicQuantum.QFT.Amplitude
import SymbolicQuantum.QFT.Dirichlet

/-
  Counting the terms of the progression, and the resulting lower bound on the
  Shor amplitude.
-/

/-- The number of steps of an arithmetic progression that stay below `M`. -/
lemma progression_count {M x₀ r : ℕ} (hr : 0 < r) (hx : x₀ < M) (j : ℕ) :
    x₀ + j * r < M ↔ j < (M - x₀ + r - 1) / r := by
  have hsucc : (j + 1) * r = j * r + r := by ring
  conv_rhs => rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hr]
  omega

/-- With the count in hand, the filter is a `range`. -/
lemma filter_progression_eq_range {M x₀ r A : ℕ} (hr : 0 < r)
    (hA : ∀ j : ℕ, x₀ + j * r < M ↔ j < A) :
    (Finset.range M).filter (fun j => x₀ + j * r < M) = Finset.range A := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    exact (hA j).mp h
  · intro h
    have h2 := (hA j).mpr h
    refine ⟨?_, h2⟩
    calc j ≤ j * r := Nat.le_mul_of_pos_right j hr
      _ ≤ x₀ + j * r := Nat.le_add_left _ _
      _ < M := h2

lemma norm_omegaPow (N : ℕ) : ‖omegaPow N‖ = 1 := by
  rw [omegaPow, Complex.norm_exp]
  simp

lemma geom_exp_eq {δ : ℝ} (j : ℕ) :
    (Complex.exp ((2 * Real.pi * δ : ℝ) * Complex.I)) ^ j
      = Complex.exp ((2 * Real.pi * δ * j : ℝ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Lower bound on the Shor amplitude.** If the phase `r·c / 2ⁿ` is within
    `1/(2A)` of an integer, the amplitude at `(c, z)` is at least `2A / (π·2ⁿ)`. -/
theorem shor_amplitude_norm_ge {n m : ℕ} (f : BitString n → BitString m)
    (c : BitString n) (z : BitString m) {r x₀ A : ℕ} {k : ℤ}
    (hr : 0 < r) (hx₀r : x₀ < r) (hApos : 0 < A)
    (hfib : ∀ x : BitString n, f x = z ↔ x.toNat % r = x₀)
    (hA : ∀ j : ℕ, x₀ + j * r < 2 ^ n ↔ j < A)
    (hδ : |((c.toNat * r : ℕ) : ℝ) / (2 ^ n) - (k : ℝ)| ≤ 1 / (2 * A)) :
    2 * A / (Real.pi * 2 ^ n) ≤ ‖app_QFT_prefix (ket_simon n m f) (combine c z)‖ := by
  have hpi := Real.pi_pos
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  rw [shor_amplitude_geom f c z hr hx₀r hfib, filter_progression_eq_range hr hA]
  have hratio : ((omegaPow (2 ^ n)) ^ c.toNat) ^ r
      = Complex.exp ((2 * Real.pi * (((c.toNat * r : ℕ) : ℝ) / (2 ^ n) - (k : ℝ)) : ℝ)
          * Complex.I) := by
    rw [← pow_mul]
    have := omegaPow_pow_eq_exp (N := 2 ^ n) (by positivity) (c.toNat * r) k
    rw [this]
    norm_num
  rw [hratio]
  simp_rw [geom_exp_eq]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_omegaPow, one_pow, one_pow, mul_one]
  have hc : ‖(1 / (2 ^ n : ℂ))‖ = 1 / (2 ^ n : ℝ) := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_two]
  rw [hc]
  have hgeom := abs_geom_sum_ge (M := A) hApos hδ
  calc 2 * A / (Real.pi * 2 ^ n) = 1 / (2 ^ n : ℝ) * (2 * A / Real.pi) := by
        field_simp
    _ ≤ 1 / (2 ^ n : ℝ) * ‖∑ x ∈ Finset.range A,
          Complex.exp ((2 * Real.pi * (((c.toNat * r : ℕ) : ℝ) / (2 ^ n) - (k : ℝ)) * x : ℝ)
            * Complex.I)‖ := by
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)

/-- The progression fits inside `2 ^ n` when the offset is at least `2 ^ n % r`.
    For smaller offsets it does not: `2 ^ n = 8`, `r = 3`, `x₀ = 0` gives `A = 3`
    and `r * A = 9`. -/
lemma progression_fits {n r x₀ A : ℕ} (hApos : 0 < A)
    (hx₀s : 2 ^ n % r ≤ x₀)
    (hA : ∀ j : ℕ, x₀ + j * r < 2 ^ n ↔ j < A) :
    r * A ≤ 2 ^ n := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  have hlast : x₀ + B * r < 2 ^ n := (hA B).mpr (by omega)
  have hdm : r * (2 ^ n / r) + 2 ^ n % r = 2 ^ n := Nat.div_add_mod _ _
  have h1 : r * B < r * (2 ^ n / r) := by nlinarith [mul_comm r B]
  have h2 : B < 2 ^ n / r := Nat.lt_of_mul_lt_mul_left h1
  calc r * (B + 1) ≤ r * (2 ^ n / r) := Nat.mul_le_mul_left r (by omega)
    _ ≤ 2 ^ n := Nat.mul_div_le _ _
