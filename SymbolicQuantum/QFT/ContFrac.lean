import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

/-
  Classical post-processing for Shor's algorithm. Measuring `c` from a register
  of size `M` leaves us with `|c/M - k/r| ≤ 1/(2M)`. Once the period is small
  enough that `2 * r ^ 2 ≤ M`, Legendre's theorem turns that into an exact
  identification: `k/r` is one of the continued-fraction convergents of `c/M`.
-/

/-- The strict Diophantine bound Legendre's theorem asks for. The measurement
bound `1/(2M)` is at most `1/(4r²)`, which leaves room below `1/(2r²)`. -/
lemma approx_bound_strict {c M k r : ℕ} (hr : 0 < r) (hM : 0 < M)
    (hsmall : 2 * r ^ 2 ≤ M)
    (happrox : |(c : ℝ) / M - (k : ℝ) / r| ≤ 1 / (2 * M)) :
    |(c : ℝ) / M - (k : ℝ) / r| < 1 / (2 * (r : ℝ) ^ 2) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hsm : 2 * (r : ℝ) ^ 2 ≤ M := by exact_mod_cast hsmall
  have hsq : (0 : ℝ) < 2 * (r : ℝ) ^ 2 := by positivity
  calc |(c : ℝ) / M - (k : ℝ) / r|
      ≤ 1 / (2 * M) := happrox
    _ ≤ 1 / (2 * (2 * (r : ℝ) ^ 2)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ < 1 / (2 * (r : ℝ) ^ 2) := one_div_lt_one_div_of_lt hsq (by linarith)

/-- The denominator of `k/r` is `r` exactly when the two are coprime. -/
private lemma den_eq {k r : ℕ} (hr : 0 < r) (hkr : Nat.Coprime k r) :
    ((k : ℚ) / r).den = r := by
  have h : (((k : ℤ) : ℚ) / ((r : ℤ) : ℚ)).den = r := by
    have := Rat.den_div_eq_of_coprime (a := (k : ℤ)) (b := (r : ℤ))
      (by exact_mod_cast hr) (by simpa using hkr)
    exact_mod_cast this
  simpa using h

/-- Shor's post-processing step: under the smallness condition `2r² ≤ M`, the
fraction `k/r` is a convergent of the continued fraction expansion of `c/M`. -/
theorem period_is_convergent {c M k r : ℕ} (hr : 0 < r) (hM : 0 < M)
    (hkr : Nat.Coprime k r) (hsmall : 2 * r ^ 2 ≤ M)
    (happrox : |(c : ℝ) / M - (k : ℝ) / r| ≤ 1 / (2 * M)) :
    ∃ n, (GenContFract.of ((c : ℝ) / M)).convs n = (k : ℝ) / r := by
  obtain ⟨n, hn⟩ := Real.exists_convs_eq_rat (ξ := (c : ℝ) / M) (q := (k : ℚ) / r) (by
    rw [den_eq hr hkr]
    push_cast
    exact approx_bound_strict hr hM hsmall happrox)
  exact ⟨n, by rw [hn]; push_cast; ring⟩
