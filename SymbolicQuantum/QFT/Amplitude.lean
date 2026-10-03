import SymbolicQuantum.QFT.Orthogonality
import SymbolicQuantum.Simon.Defs

/-
  The QFT acting on the first register, and the amplitude it produces on the
  state the oracle prepares. This is the QFT analogue of `simon_amplitude_sum`.
-/

/-- The QFT applied to the first `n` of `n + m` qubits. -/
noncomputable def app_QFT_prefix {n m : ℕ} (ψ : QState (n + m)) : QState (n + m) :=
  fun bs =>
    (1 / Real.sqrt (2 ^ n) : ℂ) *
      ∑ x : BitString n,
        (omegaPow (2 ^ n)) ^
            ((x.toNat : ℤ) * ((BitString.toNat fun i : Fin n => bs ⟨i, by omega⟩) : ℤ)) *
          ψ (combine x fun i : Fin m => bs ⟨n + i, by omega⟩)

/-- Reading the two registers back out of `combine`. -/
lemma fst_combine {n m : ℕ} (x : BitString n) (z : BitString m) :
    (fun i : Fin n => combine x z ⟨i, by omega⟩) = x := by
  funext i
  simp [combine]

lemma snd_combine {n m : ℕ} (x : BitString n) (z : BitString m) :
    (fun i : Fin m => combine x z ⟨n + i, by omega⟩) = z := by
  funext i
  simp [combine]

/-- The amplitude of measuring `(c, z)` after the QFT: a normalised sum over the
    fibre of `f` above `z`. -/
theorem app_QFT_prefix_ket_simon {n m : ℕ} (f : BitString n → BitString m)
    (c : BitString n) (z : BitString m) :
    app_QFT_prefix (ket_simon n m f) (combine c z)
      = (1 / (2 ^ n : ℂ)) *
          ∑ x ∈ Finset.univ.filter (fun x : BitString n => f x = z),
            (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * (c.toNat : ℤ)) := by
  have h2 : ((2:ℝ) ^ n) ≠ 0 := by positivity
  have hsqrt : (Real.sqrt ((2:ℝ) ^ n) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  simp only [app_QFT_prefix, fst_combine, snd_combine]
  have hval : ∀ x : BitString n,
      ket_simon n m f (combine x z)
        = if f x = z then (1 / Real.sqrt (2 ^ n) : ℂ) else 0 := by
    intro x
    simp only [ket_simon, fst_combine, snd_combine]
    by_cases h : f x = z
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hc => h hc.symm), if_neg h]
  simp only [hval]
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = z
  · rw [if_pos h, if_pos h]
    rw [show ((2:ℂ) ^ n) = (Real.sqrt ((2:ℝ) ^ n) : ℂ) * (Real.sqrt ((2:ℝ) ^ n) : ℂ) by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring]
    field_simp
  · rw [if_neg h, if_neg h]
    ring

/-
  A residue class below `M` is an arithmetic progression, so a sum of powers
  over it is geometric. This is what makes the Dirichlet bound applicable.
-/

theorem sum_residue_class_reindex {M r c : ℕ} (hrpos : 0 < r) (hc : c < r) (g : ℕ → ℂ) :
    ∑ k ∈ (Finset.range M).filter (fun k => k % r = c), g k
      = ∑ j ∈ (Finset.range M).filter (fun j => c + j * r < M), g (c + j * r) := by
  have himg : (Finset.range M).filter (fun k => k % r = c)
      = ((Finset.range M).filter (fun j => c + j * r < M)).image (fun j => c + j * r) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hkM, hkr⟩
      have hkey : c + k / r * r = k := by
        have h := Nat.div_add_mod k r
        rw [hkr, mul_comm] at h
        linarith
      exact ⟨k / r, ⟨lt_of_le_of_lt (Nat.div_le_self k r) hkM, by rw [hkey]; exact hkM⟩, hkey⟩
    · rintro ⟨j, ⟨-, hlt⟩, rfl⟩
      exact ⟨hlt, by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]⟩
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  have hmul : a * r = b * r := by linarith
  exact Nat.eq_of_mul_eq_mul_right hrpos hmul

theorem sum_residue_class_geom {M r c : ℕ} (hrpos : 0 < r) (hc : c < r) (θ : ℂ) :
    ∑ k ∈ (Finset.range M).filter (fun k => k % r = c), θ ^ k
      = θ ^ c * ∑ j ∈ (Finset.range M).filter (fun j => c + j * r < M), (θ ^ r) ^ j := by
  rw [sum_residue_class_reindex hrpos hc (fun k => θ ^ k), Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [pow_add, pow_mul']

/- Transferring a sum over bitstrings to a sum over their numeric values. -/

theorem sum_bitString_filter_toNat {n : ℕ} (P : BitString n → Prop) [DecidablePred P]
    (Q : ℕ → Prop) [DecidablePred Q] (hPQ : ∀ x : BitString n, P x ↔ Q x.toNat) (g : ℕ → ℂ) :
    ∑ x ∈ Finset.univ.filter P, g x.toNat
      = ∑ k ∈ (Finset.range (2 ^ n)).filter Q, g k := by
  have himg : (Finset.univ.filter P).image (BitString.toNat (n := n))
      = (Finset.range (2 ^ n)).filter Q := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨BitString.toNat_lt x, (hPQ x).mp hx⟩
    · rintro ⟨hk, hQ⟩
      refine ⟨bitStringEquivFin.symm ⟨k, hk⟩, ?_, ?_⟩
      · rw [hPQ]
        simpa [BitString.toNat] using hQ
      · simp [BitString.toNat]
  rw [← himg, Finset.sum_image]
  intro a _ b _ hab
  exact BitString.toNat_injective hab

lemma omegaPow_zpow_mul {N : ℕ} (a b : ℕ) :
    (omegaPow N) ^ ((a : ℤ) * (b : ℤ)) = ((omegaPow N) ^ b) ^ a := by
  rw [← Nat.cast_mul, zpow_natCast, mul_comm, pow_mul]

/-- **The Shor amplitude is a geometric sum.** When the fibre of `f` over `z` is
    the residue class of `x₀` mod the period `r`, the QFT amplitude at `c` is a
    phase times a geometric series in `ω ^ (r * c)`. -/
theorem shor_amplitude_geom {n m : ℕ} (f : BitString n → BitString m)
    (c : BitString n) (z : BitString m) {r x₀ : ℕ} (hrpos : 0 < r) (hx₀ : x₀ < r)
    (hfib : ∀ x : BitString n, f x = z ↔ x.toNat % r = x₀) :
    app_QFT_prefix (ket_simon n m f) (combine c z)
      = (1 / (2 ^ n : ℂ)) * ((omegaPow (2 ^ n)) ^ c.toNat) ^ x₀ *
          ∑ j ∈ (Finset.range (2 ^ n)).filter (fun j => x₀ + j * r < 2 ^ n),
            (((omegaPow (2 ^ n)) ^ c.toNat) ^ r) ^ j := by
  rw [app_QFT_prefix_ket_simon]
  have hpow : ∀ x : BitString n,
      (omegaPow (2 ^ n)) ^ ((x.toNat : ℤ) * (c.toNat : ℤ))
        = ((omegaPow (2 ^ n)) ^ c.toNat) ^ x.toNat := fun x => omegaPow_zpow_mul _ _
  simp only [hpow]
  rw [sum_bitString_filter_toNat (fun x => f x = z) (fun k => k % r = x₀) hfib
        (fun k => ((omegaPow (2 ^ n)) ^ c.toNat) ^ k),
      sum_residue_class_geom hrpos hx₀]
  ring

/-- The geometric ratio in exponential form. Shifting by any integer `k` is free,
    which is how the "distance to the nearest integer" phase appears. -/
lemma omegaPow_pow_eq_exp {N : ℕ} (hN : N ≠ 0) (t : ℕ) (k : ℤ) :
    (omegaPow N) ^ t
      = Complex.exp ((2 * Real.pi * ((t : ℝ) / N - (k : ℝ)) : ℝ) * Complex.I) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [omegaPow, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  push_cast
  field_simp
  ring
