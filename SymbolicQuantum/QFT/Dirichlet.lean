import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Field.GeomSum
import SymbolicQuantum.QFT.Orthogonality

/-
  The geometric-sum bound behind phase estimation. When the phase is off by at
  most 1/(2M) the sum of M unit vectors still has length at least 2M/π.
-/

lemma two_div_pi_mul_abs_le_abs_sin {t : ℝ} (ht : |t| ≤ Real.pi / 2) :
    2 / Real.pi * |t| ≤ |Real.sin t| := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]))]
    exact Real.mul_le_sin h ht
  · have h0 : 0 ≤ -t := by linarith
    have ht' : -t ≤ Real.pi / 2 := by rw [abs_of_neg h] at ht; linarith
    rw [abs_of_neg h, ← abs_neg (Real.sin t), ← Real.sin_neg,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]))]
    exact Real.mul_le_sin h0 ht'

lemma norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hsin2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rwa [show (2:ℝ) * (θ / 2) = θ by ring] at h
  have hcos2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul' (θ / 2)
    rw [show (2:ℝ) * (θ / 2) = θ by ring] at h
    have hp := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hre : (Complex.exp ((θ : ℂ) * Complex.I) - 1).re = Real.cos θ - 1 := by
    simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have him : (Complex.exp ((θ : ℂ) * Complex.I) - 1).im = Real.sin θ := by
    simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Complex.norm_def, Complex.normSq_apply, hre, him]
  have habs : (2 * |Real.sin (θ / 2)|) ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  have hgoal : (Real.cos θ - 1) * (Real.cos θ - 1) + Real.sin θ * Real.sin θ
      = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [habs, hcos2, hsin2]
    have hp := Real.sin_sq_add_cos_sq (θ / 2)
    nlinarith [hp]
  rw [hgoal]
  exact Real.sqrt_sq (by positivity)

theorem abs_geom_sum_ge {M : ℕ} (hM : 0 < M) {δ : ℝ} (hδ : |δ| ≤ 1 / (2 * M)) :
    2 * M / Real.pi ≤ ‖∑ x ∈ Finset.range M, Complex.exp ((2 * Real.pi * δ * x : ℝ) * Complex.I)‖ := by
  have hpi := Real.pi_pos
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hterm : ∀ x : ℕ,
      Complex.exp ((2 * Real.pi * δ * x : ℝ) * Complex.I)
        = (Complex.exp ((2 * Real.pi * δ : ℝ) * Complex.I)) ^ x := by
    intro x
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  set ω : ℂ := Complex.exp ((2 * Real.pi * δ : ℝ) * Complex.I) with hω
  -- |δ| * M ≤ 1/2, the form both branches need
  have hδM : |δ| * M ≤ 1 / 2 := by
    have h2M : (0:ℝ) < 2 * M := by positivity
    rw [le_div_iff₀ h2M] at hδ
    nlinarith
  have hδhalf : |δ| ≤ 1 / 2 := by nlinarith [abs_nonneg δ]
  by_cases hd : δ = 0
  · have hω1 : ω = 1 := by rw [hω, hd]; norm_num
    rw [hω1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      Complex.norm_natCast]
    rw [div_le_iff₀ hpi]
    nlinarith [Real.two_le_pi]
  · have hdabs : 0 < |δ| := abs_pos.mpr hd
    have hne : ω ≠ 1 := by
      rw [hω, Ne, Complex.exp_eq_one_iff]
      rintro ⟨k, hk⟩
      have him : 2 * Real.pi * δ = (k : ℝ) * (2 * Real.pi) := by
        have h := congrArg Complex.im hk
        simpa using h
      have hreal : δ = (k : ℝ) := by
        have hz : 2 * Real.pi * (δ - (k:ℝ)) = 0 := by linarith
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (by positivity)
        · linarith
      have hk0 : k ≠ 0 := by rintro rfl; rw [hreal] at hdabs; simp at hdabs
      have hge : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk0
      rw [hreal] at hδhalf
      linarith
    rw [geom_sum_eq hne, norm_div]
    rw [(hterm M).symm, hω, norm_exp_mul_I_sub_one, norm_exp_mul_I_sub_one,
      show (2 * Real.pi * δ * M) / 2 = Real.pi * δ * M by ring,
      show (2 * Real.pi * δ) / 2 = Real.pi * δ by ring,
      mul_div_mul_left _ _ (two_ne_zero)]
    have hexpand : |Real.pi * δ * M| = Real.pi * |δ| * M := by
      rw [abs_mul, abs_mul, abs_of_pos hpi, abs_of_nonneg hMR.le]
    have hdexpand : |Real.pi * δ| = Real.pi * |δ| := by
      rw [abs_mul, abs_of_pos hpi]
    have hbigbound : |Real.pi * δ * M| ≤ Real.pi / 2 := by
      rw [hexpand]; nlinarith
    have hsmall : |Real.pi * δ| ≤ Real.pi / 2 := by
      rw [hdexpand]; nlinarith
    have hnumlb : 2 / Real.pi * |Real.pi * δ * M| ≤ |Real.sin (Real.pi * δ * M)| :=
      two_div_pi_mul_abs_le_abs_sin hbigbound
    have hdenub : |Real.sin (Real.pi * δ)| ≤ |Real.pi * δ| := Real.abs_sin_le_abs
    have hdenpos : 0 < |Real.sin (Real.pi * δ)| := by
      have hjor := two_div_pi_mul_abs_le_abs_sin hsmall
      have hx : 0 < |Real.pi * δ| := by rw [hdexpand]; positivity
      have : 0 < 2 / Real.pi * |Real.pi * δ| := by positivity
      linarith
    rw [le_div_iff₀ hdenpos]
    rw [hexpand] at hnumlb
    rw [hdexpand] at hdenub
    calc 2 * M / Real.pi * |Real.sin (Real.pi * δ)|
        ≤ 2 * M / Real.pi * (Real.pi * |δ|) :=
          mul_le_mul_of_nonneg_left hdenub (by positivity)
      _ = 2 / Real.pi * (Real.pi * |δ| * M) := by field_simp
      _ ≤ |Real.sin (Real.pi * δ * M)| := hnumlb

/-
  Phase estimation, in normalised form: if the phase is within 1/(2M) of an
  integer, the measurement succeeds with probability at least 4/π² ≈ 0.405.
-/

theorem qft_peak_amplitude {M : ℕ} (hM : 0 < M) {φ : ℝ} (hφ : |φ| ≤ 1 / (2 * M)) :
    2 / Real.pi ≤
      ‖(M : ℂ)⁻¹ * ∑ x ∈ Finset.range M, Complex.exp ((2 * Real.pi * φ * x : ℝ) * Complex.I)‖ := by
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div, le_div_iff₀ hMR]
  calc 2 / Real.pi * M = 2 * M / Real.pi := by ring
    _ ≤ _ := abs_geom_sum_ge hM hφ

theorem qft_peak_probability {M : ℕ} (hM : 0 < M) {φ : ℝ} (hφ : |φ| ≤ 1 / (2 * M)) :
    4 / Real.pi ^ 2 ≤
      ‖(M : ℂ)⁻¹ * ∑ x ∈ Finset.range M, Complex.exp ((2 * Real.pi * φ * x : ℝ) * Complex.I)‖ ^ 2 := by
  have hpi := Real.pi_pos
  have h0 : (0:ℝ) ≤ 2 / Real.pi := by positivity
  calc 4 / Real.pi ^ 2 = (2 / Real.pi) ^ 2 := by rw [div_pow]; norm_num
    _ ≤ _ := pow_le_pow_left₀ h0 (qft_peak_amplitude hM hφ) 2
