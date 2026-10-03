import SymbolicQuantum.QFT.Bound
import SymbolicQuantum.QFT.ModExp
import SymbolicQuantum.QFT.ContFrac
import SymbolicQuantum.Shor.Reduction
import SymbolicQuantum.Simon.Defs

/-
  Shor's algorithm end to end: the quantum amplitude bound for the modular
  exponentiation oracle, period recovery by continued fractions, and the
  classical reduction to a non-trivial factor.
-/

/-- **Quantum step.** Running the oracle `x ↦ a ^ x mod N` and the QFT, the
    amplitude at a `c` whose phase `r·c / 2ⁿ` is within `1/(2A)` of an integer
    is at least `2A / (π·2ⁿ)`. -/
theorem shor_modExp_amplitude_norm_ge
    {N a n m r x₀ A : ℕ} {k : ℤ} (hN : 0 < N) (hNm : N ≤ 2 ^ m)
    (hr : is_period a r N) (hrpos : 0 < r) (hx₀r : x₀ < r) (hApos : 0 < A)
    (c x₀bs : BitString n) (hx₀bs : x₀bs.toNat % r = x₀)
    (hA : ∀ j : ℕ, x₀ + j * r < 2 ^ n ↔ j < A)
    (hδ : |((c.toNat * r : ℕ) : ℝ) / (2 ^ n) - (k : ℝ)| ≤ 1 / (2 * A)) :
    2 * A / (Real.pi * 2 ^ n)
      ≤ ‖app_QFT_prefix (ket_simon n m (modExpFun a N n m hN hNm))
          (combine c (modExpFun a N n m hN hNm x₀bs))‖ := by
  refine shor_amplitude_norm_ge _ c _ hrpos hx₀r hApos ?_ hA hδ
  intro x
  rw [modExpFun_fibre hN hNm hr hrpos x₀bs x, hx₀bs]

/-- **Measurement probability.** The probability of reading `c` off the first
    register is at least the square of the single-fibre amplitude bound. -/
theorem shor_prob_measure_ge {n m : ℕ} (f : BitString n → BitString m)
    (c : BitString n) (z : BitString m) {r x₀ A : ℕ} {k : ℤ}
    (hrpos : 0 < r) (hx₀r : x₀ < r) (hApos : 0 < A)
    (hfib : ∀ x : BitString n, f x = z ↔ x.toNat % r = x₀)
    (hA : ∀ j : ℕ, x₀ + j * r < 2 ^ n ↔ j < A)
    (hδ : |((c.toNat * r : ℕ) : ℝ) / (2 ^ n) - (k : ℝ)| ≤ 1 / (2 * A)) :
    (2 * A / (Real.pi * 2 ^ n)) ^ 2
      ≤ prob_measure_y (app_QFT_prefix (ket_simon n m f)) c := by
  have hamp := shor_amplitude_norm_ge f c z hrpos hx₀r hApos hfib hA hδ
  have hnn : (0:ℝ) ≤ 2 * A / (Real.pi * 2 ^ n) := by positivity
  have hsingle : Complex.normSq (app_QFT_prefix (ket_simon n m f) (combine c z))
      ≤ prob_measure_y (app_QFT_prefix (ket_simon n m f)) c := by
    refine Finset.single_le_sum (f := fun w : BitString m =>
      Complex.normSq (app_QFT_prefix (ket_simon n m f) (combine c w)))
      (fun w _ => Complex.normSq_nonneg _) (Finset.mem_univ z)
  calc (2 * A / (Real.pi * 2 ^ n)) ^ 2
      ≤ ‖app_QFT_prefix (ket_simon n m f) (combine c z)‖ ^ 2 :=
        pow_le_pow_left₀ hnn hamp 2
    _ = Complex.normSq (app_QFT_prefix (ket_simon n m f) (combine c z)) :=
        (Complex.normSq_eq_norm_sq _).symm
    _ ≤ _ := hsingle

/-- **Shor's algorithm.** Given a measurement `c` close enough to a multiple of
    `1/r`, the period is recoverable as a continued-fraction convergent, and the
    period yields a non-trivial factor of `N`. -/
theorem shors_algorithm {N a r c M k : ℕ}
    (hN : N > 2) (ha : 1 < a ∧ a < N) (hcop : Nat.gcd a N = 1)
    (hr : is_period a r N) (hrpos : 0 < r)
    (hsuccess : shor_success_conditions a r N)
    (hM : 0 < M) (hkr : Nat.Coprime k r) (hsmall : 2 * r ^ 2 ≤ M)
    (happrox : |(c : ℝ) / M - (k : ℝ) / r| ≤ 1 / (2 * M)) :
    (∃ i, (GenContFract.of ((c : ℝ) / M)).convs i = (k : ℝ) / r)
      ∧ (is_nontrivial_factor (Nat.gcd (a ^ (r / 2) - 1) N) N
          ∨ is_nontrivial_factor (Nat.gcd (a ^ (r / 2) + 1) N) N) :=
  ⟨period_is_convergent hrpos hM hkr hsmall happrox,
   shors_classical_reduction a r N hN ha hcop hr hsuccess⟩

/-- **Shor's algorithm, end to end.** From a measurement `c` of the first
    register satisfying the standard approximation bound: the outcome is likely,
    the period is recoverable by continued fractions, and the period yields a
    non-trivial factor of `N`.

    `2 ^ n % r ≤ x₀` picks a fibre whose progression fits inside `2 ^ n`. There
    are `r - 2 ^ n % r` such offsets, so one always exists. -/
theorem shors_algorithm_end_to_end
    {N a n m r x₀ A k : ℕ}
    (hN : N > 2) (ha : 1 < a ∧ a < N) (hcop : Nat.gcd a N = 1)
    (hNpos : 0 < N) (hNm : N ≤ 2 ^ m)
    (hr : is_period a r N) (hrpos : 0 < r)
    (hsuccess : shor_success_conditions a r N)
    (hx₀r : x₀ < r) (hApos : 0 < A) (hx₀s : 2 ^ n % r ≤ x₀)
    (c x₀bs : BitString n) (hx₀bs : x₀bs.toNat % r = x₀)
    (hA : ∀ j : ℕ, x₀ + j * r < 2 ^ n ↔ j < A)
    (hkr : Nat.Coprime k r) (hsmall : 2 * r ^ 2 ≤ 2 ^ n)
    (happrox : |(c.toNat : ℝ) / 2 ^ n - (k : ℝ) / r| ≤ 1 / (2 * 2 ^ n)) :
    (2 * A / (Real.pi * 2 ^ n)) ^ 2
        ≤ prob_measure_y
            (app_QFT_prefix (ket_simon n m (modExpFun a N n m hNpos hNm))) c
      ∧ (∃ i, (GenContFract.of ((c.toNat : ℝ) / 2 ^ n)).convs i = (k : ℝ) / r)
      ∧ (is_nontrivial_factor (Nat.gcd (a ^ (r / 2) - 1) N) N
          ∨ is_nontrivial_factor (Nat.gcd (a ^ (r / 2) + 1) N) N) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hrpos
  have hAR : (0:ℝ) < A := by exact_mod_cast hApos
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have hAr : r * A ≤ 2 ^ n := progression_fits hApos hx₀s hA
  have hArR : (r:ℝ) * A ≤ 2 ^ n := by exact_mod_cast hAr
  -- the quantum-side phase bound follows from the classical approximation
  have hδ : |((c.toNat * r : ℕ) : ℝ) / (2 ^ n) - ((k : ℤ) : ℝ)| ≤ 1 / (2 * A) := by
    have key : ((c.toNat * r : ℕ) : ℝ) / (2 ^ n) - ((k : ℤ) : ℝ)
        = r * ((c.toNat : ℝ) / 2 ^ n - (k : ℝ) / r) := by
      push_cast
      field_simp
    rw [key, abs_mul, abs_of_pos hrR]
    calc (r:ℝ) * |(c.toNat : ℝ) / 2 ^ n - (k : ℝ) / r|
        ≤ (r:ℝ) * (1 / (2 * 2 ^ n)) := mul_le_mul_of_nonneg_left happrox hrR.le
      _ ≤ 1 / (2 * A) := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * A)]
          field_simp
          nlinarith
  have hfib : ∀ x : BitString n,
      modExpFun a N n m hNpos hNm x = modExpFun a N n m hNpos hNm x₀bs
        ↔ x.toNat % r = x₀ := by
    intro x
    rw [modExpFun_fibre hNpos hNm hr hrpos x₀bs x, hx₀bs]
  have hcast : ((2 ^ n : ℕ) : ℝ) = (2:ℝ) ^ n := by push_cast; ring
  have hconv := period_is_convergent (c := c.toNat) (M := 2 ^ n) (k := k) (r := r)
      hrpos (Nat.two_pow_pos n) hkr (by exact_mod_cast hsmall)
      (by rw [hcast]; exact happrox)
  rw [hcast] at hconv
  exact ⟨shor_prob_measure_ge (modExpFun a N n m hNpos hNm) c
      (modExpFun a N n m hNpos hNm x₀bs) hrpos hx₀r hApos hfib hA hδ,
    hconv,
    shors_classical_reduction a r N hN ha hcop hr hsuccess⟩

/-- The same statement with the progression count computed, so neither `A` nor
    its characterisation has to be supplied by the caller. -/
theorem shors_algorithm_concrete
    {N a n m r x₀ k : ℕ}
    (hN : N > 2) (ha : 1 < a ∧ a < N) (hcop : Nat.gcd a N = 1)
    (hNpos : 0 < N) (hNm : N ≤ 2 ^ m)
    (hr : is_period a r N) (hrpos : 0 < r)
    (hsuccess : shor_success_conditions a r N)
    (hx₀r : x₀ < r) (hx₀n : x₀ < 2 ^ n) (hx₀s : 2 ^ n % r ≤ x₀)
    (c x₀bs : BitString n) (hx₀bs : x₀bs.toNat % r = x₀)
    (hkr : Nat.Coprime k r) (hsmall : 2 * r ^ 2 ≤ 2 ^ n)
    (happrox : |(c.toNat : ℝ) / 2 ^ n - (k : ℝ) / r| ≤ 1 / (2 * 2 ^ n)) :
    (2 * (((2 ^ n - x₀ + r - 1) / r : ℕ) : ℝ) / (Real.pi * 2 ^ n)) ^ 2
        ≤ prob_measure_y
            (app_QFT_prefix (ket_simon n m (modExpFun a N n m hNpos hNm))) c
      ∧ (∃ i, (GenContFract.of ((c.toNat : ℝ) / 2 ^ n)).convs i = (k : ℝ) / r)
      ∧ (is_nontrivial_factor (Nat.gcd (a ^ (r / 2) - 1) N) N
          ∨ is_nontrivial_factor (Nat.gcd (a ^ (r / 2) + 1) N) N) :=
  shors_algorithm_end_to_end hN ha hcop hNpos hNm hr hrpos hsuccess hx₀r
    (Nat.div_pos (by omega) hrpos) hx₀s c x₀bs hx₀bs
    (progression_count hrpos hx₀n) hkr hsmall happrox

/-
  The side conditions are satisfiable, so the statements above are not vacuous.
-/

/-- An offset meeting all three conditions exists, together with a bitstring
    carrying it. `x₀ = 2 ^ n % r` works. -/
lemma exists_offset {n r : ℕ} (hrpos : 0 < r) (hrn : r ≤ 2 ^ n) :
    ∃ (x₀ : ℕ) (x₀bs : BitString n),
      x₀ < r ∧ x₀ < 2 ^ n ∧ 2 ^ n % r ≤ x₀ ∧ x₀bs.toNat % r = x₀ := by
  have hlt : 2 ^ n % r < r := Nat.mod_lt _ hrpos
  refine ⟨2 ^ n % r, bitStringEquivFin.symm ⟨2 ^ n % r, by omega⟩, hlt, by omega, le_rfl, ?_⟩
  simp [BitString.toNat, Nat.mod_eq_of_lt hlt]

/-- A measurement meeting the approximation bound exists: round `k · 2ⁿ / r`. -/
lemma exists_good_measurement {n r k : ℕ} (hrpos : 0 < r) :
    ∃ c : ℤ, |(c : ℝ) / 2 ^ n - (k : ℝ) / r| ≤ 1 / (2 * 2 ^ n) := by
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have hrR : (0:ℝ) < r := by exact_mod_cast hrpos
  refine ⟨round ((k : ℝ) * 2 ^ n / r), ?_⟩
  have hkey : (round ((k : ℝ) * 2 ^ n / r) : ℝ) / 2 ^ n - (k : ℝ) / r
      = -(((k : ℝ) * 2 ^ n / r - round ((k : ℝ) * 2 ^ n / r)) / 2 ^ n) := by
    field_simp
    ring
  rw [hkey, abs_neg, abs_div, abs_of_pos h2n, div_le_iff₀ h2n]
  calc |(k : ℝ) * 2 ^ n / r - round ((k : ℝ) * 2 ^ n / r)| ≤ 1 / 2 := abs_sub_round _
    _ = 1 / (2 * 2 ^ n) * 2 ^ n := by field_simp
