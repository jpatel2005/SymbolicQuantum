import SymbolicQuantum.QuantumTactics
import SymbolicQuantum.Shor.Defs
import SymbolicQuantum.Shor.ReductionLemmas
import SymbolicQuantum.GlobalPhase
import SymbolicQuantum.QuantumLemmas

open Classical

/-
  Reduction from Factoring to Order-Finding
-/

/- Shor's Success Conditions -/

-- Given that N divides the product (x - 1)(x + 1), and x is not congruent
-- to ±1 mod N, then one of the two GCDs will yield a non-trivial factor of N.
lemma gcd_nontrivial_from_product (x N : ℕ)
  (hx : 1 ≤ x)
  (h : N ∣ (x - 1) * (x + 1))
  (hN : N > 2)
  (h_not_one : (x : ZMod N) ≠ 1)
  (h_not_minus_one : (x : ZMod N) ≠ -1) :
  is_nontrivial_factor (Nat.gcd (x - 1) N) N ∨
  is_nontrivial_factor (Nat.gcd (x + 1) N) N := by {
  have h_N_ndvd_xm1 : ¬(N ∣ (x - 1)) := by
    intro h_dvd
    apply h_not_one
    have h0 := (zmod_eq_zero_iff_dvd (x - 1)).mpr h_dvd
    rw [Nat.cast_sub hx, sub_eq_zero] at h0
    exact_mod_cast h0
  have h_N_ndvd_xp1 : ¬(N ∣ (x + 1)) := by
    intro h_dvd
    apply h_not_minus_one
    have h0 := (zmod_eq_zero_iff_dvd (x + 1)).mpr h_dvd
    push_cast at h0
    calc (↑x : ZMod N) = ↑x + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h0]
      _ = -1 := by ring
  left
  refine ⟨?_, ?_, Nat.gcd_dvd_right _ _⟩
  · by_contra h_le
    push_neg at h_le
    have h_cop : Nat.gcd (x - 1) N = 1 := by
      have := Nat.gcd_pos_of_pos_right (x - 1) (show 0 < N by omega)
      omega
    exact h_N_ndvd_xp1 ((Nat.Coprime.symm h_cop).dvd_of_dvd_mul_left h)
  · exact lt_of_le_of_ne
      (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _))
      (fun h_eq => h_N_ndvd_xm1 (h_eq ▸ Nat.gcd_dvd_left _ _))
}

/- Classical Reduction Theorem: Factoring to Order Finding -/

/-- If we find the period r, and it meets the success conditions,
    then one of the two GCD equations will output a non-trivial factor of N. -/
theorem shors_classical_reduction (a r N : ℕ)
(h_N : N > 2)
(h_a : 1 < a ∧ a < N)
(h_coprime : Nat.gcd a N = 1)
(h_period : is_period a r N)
(h_success : shor_success_conditions a r N) :
is_nontrivial_factor (Nat.gcd ((a ^ (r / 2)) - 1) N) N ∨
is_nontrivial_factor (Nat.gcd ((a ^ (r / 2)) + 1) N) N := by {
  have h_even : Even r := h_success.1
  have h_not_minus_one : (a : ZMod N) ^ (r / 2) ≠ -1 := h_success.2
  have h_pow_r_eq_one : (a : ZMod N) ^ r = 1 := by {
    unfold is_period at h_period
    rw [← h_period]
    exact pow_orderOf_eq_one _
  }
  have h_sq_eq_one : ((a : ZMod N) ^ (r / 2)) ^ 2 = 1 :=
    shor_key_identity a r N h_pow_r_eq_one h_even

  have h_prod_eq_zero : ((a : ZMod N) ^ (r / 2) - 1) * ((a : ZMod N) ^ (r / 2) + 1) = 0 := by {
    rw [←factorization_identity]
    ring_nf
    rw [pow_mul, h_sq_eq_one]
    simp
  }

  have h_divides : N ∣ ((a ^ (r / 2) - 1) * (a ^ (r / 2) + 1)) := by {
    rw [← zmod_eq_zero_iff_dvd]
    have h1 : 1 ≤ a ^ (r / 2) := Nat.one_le_pow _ _ (by linarith [h_a.1])
    simp [Nat.cast_sub h1]
    exact h_prod_eq_zero
  }

  have h_not_one : (a : ZMod N) ^ (r / 2) ≠ 1 := by {
    unfold is_period at h_period
    intro h_eq_one
    have h_ord_dvd : r ∣ r / 2 := by
      nth_rw 1 [← h_period]
      exact orderOf_dvd_of_pow_eq_one h_eq_one
    have hr_pos : 0 < r := by
      haveI : NeZero N := ⟨by linarith⟩
      let u : (ZMod N)ˣ := ZMod.unitOfCoprime a h_coprime
      have horder : orderOf u = r := by
        have hinj := orderOf_injective (Units.coeHom (ZMod N)) Units.val_injective u
        rw [Units.coeHom_apply, ZMod.coe_unitOfCoprime, h_period] at hinj
        exact hinj.symm
      rw [← horder]
      exact orderOf_pos u
    have h_lt : r / 2 < r := Nat.div_lt_self hr_pos (by norm_num)
    have h_r_dvd_pos : 0 < r / 2 := by {
      obtain ⟨k, hk⟩ := h_even
      omega
    }
    exact absurd (Nat.le_of_dvd h_r_dvd_pos h_ord_dvd) (by omega)
  }

  have hx : 1 ≤ a ^ (r / 2) := Nat.one_le_pow _ _ (by linarith [h_a.1])

  have h_divides : N ∣ ((a ^ (r / 2) - 1) * (a ^ (r / 2) + 1)) := by {
    rw [← zmod_eq_zero_iff_dvd]
    simp [Nat.cast_sub hx]
    exact h_prod_eq_zero
  }

  have h_not_one_cast : ((a ^ (r / 2) : ℕ) : ZMod N) ≠ 1 := by {
    push_cast
    exact h_not_one
  }

  have h_not_minus_one_cast : ((a ^ (r / 2) : ℕ) : ZMod N) ≠ -1 := by {
    push_cast
    exact h_not_minus_one
  }

  exact gcd_nontrivial_from_product (a ^ (r / 2)) N hx h_divides h_N h_not_one_cast h_not_minus_one_cast
}

/-
  Classical preprocessing checks:
  (1) N is odd
  (2) N is composite
  (3) N is not of the form p^k for p-prime and k > 1

  If these checks are passed, then at least half of the valid choices of a
  will satisfy the success conditions. That is, the probability of success is at least 1/2.
-/

/-- For distinct odd primes p, q, valid_choices(p*q) has cardinality (p-1)(q-1) - 1.
    This is Euler's totient φ(pq) = (p-1)(q-1), minus the excluded element a = 1.
    (a = 0 is already excluded since gcd(0, pq) = pq ≠ 1.) -/
lemma valid_choices_card_semiprime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (_hp2 : p ≠ 2) (_hq2 : q ≠ 2) :
    (valid_choices (p * q)).card = (p - 1) * (q - 1) - 1 := by
  -- The coprime set S = {a ∈ range(pq) | gcd(a, pq) = 1} has card (p-1)(q-1)
  set S := (Finset.range (p * q)).filter (fun a => Nat.gcd a (p * q) = 1) with hS_def
  -- 1 is in the coprime set
  have h1_mem : 1 ∈ S := by
    rw [hS_def, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := Nat.mul_le_mul hp.two_le hq.two_le; omega, Nat.gcd_one_left _⟩
  -- valid_choices = S \ {1}: elements > 1 that are coprime
  have h_vc : valid_choices (p * q) = S.erase 1 := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_erase]
      unfold valid_choices at ha
      rw [Finset.mem_filter] at ha
      exact ⟨by omega, by rw [hS_def, Finset.mem_filter]; exact ⟨ha.1, ha.2.2⟩⟩
    · intro ha
      rw [Finset.mem_erase] at ha
      obtain ⟨ha_ne, ha_S⟩ := ha
      rw [hS_def, Finset.mem_filter, Finset.mem_range] at ha_S
      unfold valid_choices
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨ha_S.1, ?_, ha_S.2⟩
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [Nat.gcd_zero_left] at ha_S
        exact absurd ha_S.2 (by have := Nat.mul_le_mul hp.two_le hq.two_le; omega)
      omega
  have h_card_S : S.card = (p - 1) * (q - 1) := by
    rw [hS_def]; exact coprime_count hp hq hpq
  rw [h_vc, Finset.card_erase_of_mem h1_mem, h_card_S]

/-- At least half of (ℤ/pqℤ)* satisfies Shor's success conditions.
    Proved by connecting `successful_choices` to the CRT counting bound:
    the coprime+successful filter equals `successful_choices` because
    a = 0 is not coprime to pq, and a = 1 is not a successful choice. -/
lemma successful_choices_ge_half {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    2 * (successful_choices (p * q)).card ≥ (p - 1) * (q - 1) := by
  -- Step 1: Rewrite successful_choices as a single filter on range
  suffices h : successful_choices (p * q) =
    (Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ is_successful_choice a (p * q)) by
    rw [h]; exact crt_counting_bound hp hq hpq hp2 hq2
  -- Step 2: Combine nested filters and show predicates agree on range
  unfold successful_choices valid_choices
  rw [Finset.filter_filter]
  apply Finset.filter_congr
  intro a ha
  rw [Finset.mem_range] at ha
  -- Goal: (1 < a ∧ gcd = 1) ∧ successful ↔ gcd = 1 ∧ successful
  constructor
  · rintro ⟨⟨-, hgcd⟩, hsucc⟩; exact ⟨hgcd, hsucc⟩
  · rintro ⟨hgcd, hsucc⟩
    refine ⟨⟨?_, hgcd⟩, hsucc⟩
    -- Show 1 < a: a = 0 contradicts coprimality, a = 1 contradicts success
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [Nat.gcd_zero_left] at hgcd
      exact absurd hgcd (by have := Nat.mul_le_mul hp.two_le hq.two_le; omega)
    have ha1 : a ≠ 1 := by
      rintro rfl; exact one_not_successful_choice _ hsucc
    omega

theorem shors_probability_bound_semiprime (N : ℕ)
(h_odd : Odd N)
(h_prime_factors : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ N = p * q) :
2 * (successful_choices N).card ≥ (valid_choices N).card := by {
  obtain ⟨p, q, hp, hq, hpq, hN⟩ := h_prime_factors
  subst hN
  -- Both primes must be odd since N = p*q is odd
  have hp2 : p ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; omega
  have hq2 : q ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; omega
  -- Chain: valid.card = (p-1)(q-1) - 1 ≤ (p-1)(q-1) ≤ 2 * successful.card
  show (valid_choices (p * q)).card ≤ 2 * (successful_choices (p * q)).card
  calc (valid_choices (p * q)).card
      = (p - 1) * (q - 1) - 1 := valid_choices_card_semiprime hp hq hpq hp2 hq2
    _ ≤ (p - 1) * (q - 1) := Nat.sub_le _ _
    _ ≤ 2 * (successful_choices (p * q)).card := successful_choices_ge_half hp hq hpq hp2 hq2
}

/-- **Shor's probability bound (general).**
    If N > 1 is odd and not a prime power (i.e., has at least two distinct prime factors),
    then at least half of the valid choices of `a` satisfy Shor's success conditions.

    This generalises `shors_probability_bound_semiprime` from N = p·q to arbitrary N
    by extracting two distinct prime factors p, q ∣ N and reducing to the semiprime
    sub-case via the surjection (ℤ/Nℤ)* ↠ (ℤ/pℤ)* × (ℤ/qℤ)*. -/
theorem shors_probability_bound (N : ℕ)
    (h_odd : Odd N)
    (h_gt_one : N > 1)
    (h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k) :
    2 * (successful_choices N).card ≥ (valid_choices N).card := by
  -- Step 1: Extract two distinct prime factors
  obtain ⟨p, q, hp, hq, hpq, hpN, hqN⟩ := exists_two_distinct_prime_factors h_gt_one h_not_prime_power
  -- Step 2: Both primes are odd (since N is odd and p, q ∣ N)
  have hp2 : p ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; obtain ⟨m, hm⟩ := hpN; omega
  have hq2 : q ≠ 2 := by
    rintro rfl; obtain ⟨k, hk⟩ := h_odd; obtain ⟨m, hm⟩ := hqN; omega
  -- Step 3: Counting
  have hvc := valid_choices_card_general h_gt_one
  -- Partition coprime residues into successful and unsuccessful
  set S := (Finset.range N).filter (fun a => Nat.gcd a N = 1) with hS_def
  have hS_card : S.card = Nat.totient N := by
    unfold Nat.totient; congr 1
    apply Finset.filter_congr; intro a _
    show Nat.gcd a N = 1 ↔ Nat.Coprime N a; rw [Nat.gcd_comm]
  have h_unsucc_bound :
      2 * (S.filter (fun a => ¬is_successful_choice a N)).card ≤ Nat.totient N := by
    have : S.filter (fun a => ¬is_successful_choice a N) =
        (Finset.range N).filter (fun a => Nat.gcd a N = 1 ∧ ¬is_successful_choice a N) := by
      rw [hS_def, Finset.filter_filter]
    rw [this]; exact general_unsuccessful_bound hp hq hpq hp2 hq2 hpN hqN
  have h_partition := Finset.filter_card_add_filter_neg_card_eq_card
    (fun a => is_successful_choice a N) (s := S)
  -- successful_choices = S.filter(successful) (a=0 not coprime, a=1 not successful)
  have h_succ_eq : successful_choices N = S.filter (fun a => is_successful_choice a N) := by
    unfold successful_choices valid_choices
    rw [Finset.filter_filter, hS_def, Finset.filter_filter]
    apply Finset.filter_congr; intro a ha
    rw [Finset.mem_range] at ha
    constructor
    · rintro ⟨⟨-, hg⟩, hs⟩; exact ⟨hg, hs⟩
    · rintro ⟨hg, hs⟩
      refine ⟨⟨?_, hg⟩, hs⟩
      have ha0 : a ≠ 0 := by rintro rfl; simp at hg; omega
      have ha1 : a ≠ 1 := fun h => by subst h; exact one_not_successful_choice _ hs
      omega
  rw [hvc, h_succ_eq]
  omega
