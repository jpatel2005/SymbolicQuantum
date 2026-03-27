import SymbolicQuantum.QuantumTactics
import SymbolicQuantum.Simon.Defs
import SymbolicQuantum.GlobalPhase
import SymbolicQuantum.QuantumLemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic

open Classical

/- Definitions -/

-- A non-trivial factor is a divisor d, where 1 < d < N and d divides N
def is_nontrivial_factor (d N : ℕ) : Prop :=
  1 < d ∧ d < N ∧ d ∣ N

-- The classical modular exponentiation definition
def mod_exp (a r N : ℕ) : ZMod N :=
  (a : ZMod N) ^ r

/-
-- All integers k less than r cannot satisfy a^k ≡ 1 (mod N)
def is_period (a r N : ℕ) : Prop :=
  r > 0 ∧
  mod_exp a r N = 1 ∧
  ∀ k, 0 < k → k < r → mod_exp a k N ≠ 1
-/

def is_period (a r N : ℕ) : Prop :=
  orderOf (a : ZMod N) = r

/- Shor's Success Conditions -/

lemma factorization_identity {N : ℕ} (x : ZMod N) :
x^2 - 1 = (x - 1) * (x + 1) := by ring

-- If r is even and a^r ≡ 1 (mod N), then (a^(r/2) - 1)(a^(r/2) + 1) ≡ 0 (mod N)
lemma shor_key_identity (a r N : ℕ)
(h : (a : ZMod N) ^ r = 1)
(h_even : Even r) :
let x := (a : ZMod N) ^ (r / 2)
x ^ 2 = 1 := by {
  ring_nf
  rw [Nat.div_mul_cancel (Even.two_dvd h_even), h]
}

lemma zmod_eq_zero_iff_dvd {N : ℕ} (x : ℕ) :
((x : ZMod N) = 0) ↔ N ∣ x := by
  exact ZMod.natCast_eq_zero_iff x N


#check ZMod.natCast_zmod_eq_zero_iff_dvd
#check Nat.Coprime
#check Nat.gcd_dvd_right
#check Nat.gcd_dvd_left
#check Nat.eq_one_of_dvd_one

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
  sorry
}

-- Two conditions:
-- (1) r is even
-- (2) a^(r/2) ≡ -1 (mod N) does not hold.
def shor_success_conditions (a r N : ℕ) : Prop :=
  (Even r) ∧ ((a : ZMod N) ^ (r / 2) ≠ -1)

/- Classical Reduction Theorem: Factoring to Order Finding -/

/-- If we find the period r, and it meets the success conditions,
    then one of the two GCD equations will output a non-trivial factor of N. -/
theorem shors_classical_reduction (a r N : ℕ)
(h_N : N > 2)
(h_a : 1 < a ∧ a < N)
(h_coprime : Nat.gcd a N = 1)
(h_period : is_period a r N) -- Use your definition here!
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

/- Probability of Success -/

-- a is a successful choice if there exists a period r that satisfies the success conditions
def is_successful_choice (a N : ℕ) : Prop :=
  ∃ r, is_period a r N ∧ shor_success_conditions a r N

-- the set of valid a's; 1 < a < N and a coprime to N
noncomputable def valid_choices (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun a => 1 < a ∧ Nat.gcd a N = 1)

/-- The subset of valid 'a's that will successfully yield a factor. -/
noncomputable def successful_choices (N : ℕ) : Finset ℕ :=
  (valid_choices N).filter (fun a => is_successful_choice a N)

/-
  Classical preprocessing checks:
  (1) N is odd
  (2) N is composite
  (3) N is not of the form p^k for p-prime and k > 1

  If these checks are passed, then at least half of the valid choices of a
  will satisfy the success conditions. That is, the probability of success is at least 1/2.
-/
theorem shors_probability_bound (N : ℕ)
(h_odd : Odd N)
-- (h_composite : ¬Nat.Prime N)
-- (h_not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k)
(h_prime_factors : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ N = p * q) :
2 * (successful_choices N).card ≥ (valid_choices N).card := by {
  sorry
}
