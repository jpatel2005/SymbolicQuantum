import SymbolicQuantum.QuantumTactics
import SymbolicQuantum.Simon.Defs
import SymbolicQuantum.GlobalPhase
import SymbolicQuantum.QuantumLemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

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

/-- Element a = 1 is never a successful choice: its order is 1 (odd), so it
    fails the "even order" condition. -/
private lemma one_not_successful_choice (N : ℕ) : ¬is_successful_choice 1 N := by
  rintro ⟨r, hr, heven, -⟩
  unfold is_period at hr
  rw [Nat.cast_one, orderOf_one] at hr
  obtain ⟨k, hk⟩ := heven; omega

/-- The number of coprime residues mod pq equals (p-1)(q-1), i.e., Euler's totient φ(pq). -/
private lemma coprime_count {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    ((Finset.range (p * q)).filter (fun a => Nat.gcd a (p * q) = 1)).card
    = (p - 1) * (q - 1) := by
  -- Rewrite gcd a N = 1 to Coprime N a (totient's predicate uses Coprime N a = gcd N a = 1)
  have h_eq : (Finset.range (p * q)).filter (fun a => Nat.gcd a (p * q) = 1)
    = (Finset.range (p * q)).filter (fun a => Nat.Coprime (p * q) a) := by
    apply Finset.filter_congr
    intro a _
    show Nat.gcd a (p * q) = 1 ↔ Nat.gcd (p * q) a = 1
    rw [Nat.gcd_comm]
  rw [h_eq]
  -- Now the LHS is exactly Nat.totient (p * q)
  change Nat.totient (p * q) = (p - 1) * (q - 1)
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq),
      Nat.totient_prime hp, Nat.totient_prime hq]

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

/-- CRT sends natural number casts to the pair of casts. -/
private lemma crt_natCast_eq {m n : ℕ} (h : Nat.Coprime m n) (a : ℕ) :
    ZMod.chineseRemainder h (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) :=
  Prod.ext (by simp [ZMod.chineseRemainder])
           (by simp [ZMod.chineseRemainder])

/-- Under CRT, orderOf equals lcm of component orders. -/
private lemma orderOf_crt_eq_lcm {m n : ℕ} (h : Nat.Coprime m n) (a : ℕ) :
    orderOf (a : ZMod (m * n)) = Nat.lcm (orderOf (a : ZMod m)) (orderOf (a : ZMod n)) := by
  rw [← MulEquiv.orderOf_eq (ZMod.chineseRemainder h).toMulEquiv (a : ZMod (m * n)),
      show (ZMod.chineseRemainder h).toMulEquiv (a : ZMod (m * n)) =
        ZMod.chineseRemainder h (a : ZMod (m * n)) from rfl,
      crt_natCast_eq, Prod.orderOf_mk]

/-- Under CRT, a^k = -1 iff both components are -1. -/
private lemma pow_eq_neg_one_crt {m n : ℕ} (h : Nat.Coprime m n) (a k : ℕ) :
    (a : ZMod (m * n)) ^ k = -1 ↔
    (a : ZMod m) ^ k = -1 ∧ (a : ZMod n) ^ k = -1 := by
  let φ := ZMod.chineseRemainder h
  constructor
  · intro heq
    have h1 := congr_arg φ heq
    rw [map_pow, crt_natCast_eq, map_neg, map_one, Prod.neg_mk, Prod.pow_mk] at h1
    exact ⟨(Prod.mk.inj h1).1, (Prod.mk.inj h1).2⟩
  · intro ⟨hp, hq⟩
    apply φ.injective
    rw [map_pow, crt_natCast_eq, map_neg, map_one, Prod.neg_mk, Prod.pow_mk]
    exact Prod.mk_inj.mpr ⟨hp, hq⟩

/-- ¬is_successful_choice iff order is odd or half-power equals -1. -/
private lemma not_successful_iff (a N : ℕ) :
    ¬is_successful_choice a N ↔
    (¬Even (orderOf (a : ZMod N)) ∨
     (a : ZMod N) ^ (orderOf (a : ZMod N) / 2) = -1) := by
  unfold is_successful_choice is_period shor_success_conditions
  push_neg
  constructor
  · intro h
    by_cases heven : Even (orderOf (a : ZMod N))
    · right; exact h _ rfl heven
    · left; exact heven
  · rintro (hodd | hneg) r hr heven
    · exact absurd (hr ▸ heven) hodd
    · rw [← hr]; exact hneg

/-- If u^(n/2) ≠ 1 and orderOf u divides n, then n/orderOf u is odd. -/
private lemma div_orderOf_odd_of_pow_ne_one {G : Type*} [Group G]
    {u : G} {n : ℕ} (hdvd : orderOf u ∣ n) (h : u ^ (n / 2) ≠ 1) :
    ¬Even (n / orderOf u) := by
  intro ⟨k, hk⟩
  apply h
  -- If orderOf u = 0 then 0 ∣ n forces n = 0, so u^0 = 1, contradicting h
  have ho_pos : 0 < orderOf u := by
    by_contra h0; push_neg at h0
    have : orderOf u = 0 := by omega
    rw [this, Nat.zero_dvd] at hdvd; subst hdvd; simp at h
  -- From n / orderOf u = 2k and orderOf u | n, derive n = orderOf u * (2 * k)
  have hn : n = orderOf u * (2 * k) := by
    have h1 := Nat.div_mul_cancel hdvd  -- n / orderOf u * orderOf u = n
    rw [hk] at h1; linarith
  -- Therefore n / 2 = orderOf u * k
  have h2 : n / 2 = orderOf u * k := by
    have : n = 2 * (orderOf u * k) := by linarith
    omega
  rw [h2, pow_mul, pow_orderOf_eq_one, one_pow]

/-- A positive natural is odd iff its factorization at 2 vanishes. -/
private lemma odd_iff_factorization_two_eq_zero {n : ℕ} (hn : n ≠ 0) :
    Odd n ↔ n.factorization 2 = 0 := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  rw [Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn]
  omega

/-- For `d ∣ n`, the quotient `n / d` is odd iff `d` carries the full 2-part of `n`. -/
private lemma odd_div_iff_factorization_two_eq {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    Odd (n / d) ↔ n.factorization 2 = d.factorization 2 := by
  have hd0 : d ≠ 0 := by
    intro h
    subst h
    rw [Nat.zero_dvd] at hd
    exact hn hd
  have hnd : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
      (Nat.pos_of_ne_zero hd0)).ne'
  rw [odd_iff_factorization_two_eq_zero hnd, Nat.factorization_div hd]
  change (n.factorization 2 - d.factorization 2 = 0) ↔ n.factorization 2 = d.factorization 2
  have hle : d.factorization 2 ≤ n.factorization 2 := by
    exact (Nat.factorization_le_iff_dvd hd0 hn).2 hd 2
  omega

/-- If `n` is even and nonzero, then `gcd n k` is odd exactly when `k` is odd. -/
private lemma gcd_odd_iff_right_odd_of_left_even {n k : ℕ} (hn0 : n ≠ 0) (hn_even : Even n) :
    Odd (Nat.gcd n k) ↔ Odd k := by
  cases hk0 : k with
  | zero =>
      have hnot : ¬ Odd n := by simpa [Nat.not_even_iff_odd] using hn_even
      simpa [hk0, Nat.gcd_zero_right] using hnot
  | succ k =>
      have hkpos : Nat.succ k ≠ 0 := by simp
      have hg0 : Nat.gcd n (Nat.succ k) ≠ 0 := Nat.gcd_ne_zero_left hn0
      rw [odd_iff_factorization_two_eq_zero hg0, odd_iff_factorization_two_eq_zero hkpos]
      have hgfac :=
        congrArg (fun f => f 2) (Nat.factorization_gcd (a := n) (b := Nat.succ k) hn0 hkpos)
      simp only [Finsupp.inf_apply] at hgfac
      rw [hgfac]
      change min (n.factorization 2) ((Nat.succ k).factorization 2) = 0 ↔
        (Nat.succ k).factorization 2 = 0
      have hn2pos : 0 < n.factorization 2 := by
        have hdiv2 : 2 ∣ n := by rwa [← even_iff_two_dvd]
        exact lt_of_lt_of_le (by norm_num)
          ((Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn0).1 hdiv2)
      omega

/-- If `a * b` is even and `b` is odd, then `a` is even. -/
private lemma even_of_even_mul_odd {a b : ℕ} (hab : Even (a * b)) (hb : Odd b) :
    Even a := by
  rw [even_iff_two_dvd] at hab ⊢
  exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_two_left).2 hb) hab

/-- In `ZMod p`, the half-order power of a unit of even order is `-1`. -/
private lemma unit_pow_half_order_eq_neg_one {p : ℕ} (hp : Nat.Prime p) {x : (ZMod p)ˣ}
    (heven : Even (orderOf x)) :
    (x : ZMod p) ^ (orderOf x / 2) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsq : ((x : ZMod p) ^ (orderOf x / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel heven.two_dvd]
    simpa [orderOf_units] using pow_orderOf_eq_one (x : ZMod p)
  have hneq : (x : ZMod p) ^ (orderOf x / 2) ≠ 1 := by
    intro hx
    have hdiv : orderOf (x : ZMod p) ∣ orderOf x / 2 := orderOf_dvd_of_pow_eq_one hx
    have hpos : 0 < orderOf x := orderOf_pos x
    have hhalfpos : 0 < orderOf x / 2 := by
      obtain ⟨k, hk⟩ := heven
      omega
    rw [orderOf_units] at hdiv
    exact absurd (Nat.le_of_dvd hhalfpos hdiv) (by
      have hlt : orderOf x / 2 < orderOf x := Nat.div_lt_self hpos (by norm_num)
      omega)
  exact (sq_eq_one_iff.mp hsq).resolve_left hneq

/-- If a unit has even order and `n / orderOf x` is odd, then its `n/2`-th power is `-1`. -/
private lemma unit_pow_half_mul_odd_eq_neg_one {p : ℕ} (hp : Nat.Prime p) {x : (ZMod p)ˣ}
    {n : ℕ} (hdvd : orderOf x ∣ n) (hodd : Odd (n / orderOf x))
    (heven : Even (orderOf x)) :
    (x : ZMod p) ^ (n / 2) = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have heven' : Even (orderOf x) := heven
  obtain ⟨m, hm⟩ := hdvd
  have hquot : n / orderOf x = m := by
    rw [hm, Nat.mul_div_right _ (orderOf_pos x)]
  have hmodd : Odd m := by simpa [hquot] using hodd
  obtain ⟨k, hk⟩ := heven
  have hk2 : orderOf x / 2 = k := by
    rw [hk]
    omega
  have hmul : (k + k) * m = 2 * (k * m) := by ring
  have hn2 : n / 2 = (orderOf x / 2) * m := by
    calc
      n / 2 = ((k + k) * m) / 2 := by rw [hm, hk]
      _ = (2 * (k * m)) / 2 := by rw [hmul]
      _ = k * m := by rw [Nat.mul_div_right (k * m) (by norm_num)]
      _ = (orderOf x / 2) * m := by rw [hk2]
  rw [hn2, pow_mul, unit_pow_half_order_eq_neg_one hp heven']
  simpa using hmodd.neg_one_pow (α := ZMod p)

/-- For a generator `g` of `(ZMod p)ˣ`, the 2-part of `orderOf (g^k)` is maximal iff `k` is odd. -/
private lemma order_factorization_two_eq_generator_iff_odd {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : orderOf g = p - 1) (k : ℕ) :
    (orderOf (g ^ k)).factorization 2 = (p - 1).factorization 2 ↔ Odd k := by
  have hEven : Even (p - 1) := by
    rcases hp.odd_of_ne_two hp2 with ⟨t, ht⟩
    use t
    rw [ht]
    omega
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  have hdiv : orderOf (g ^ k) ∣ p - 1 := by
    rw [← hg]
    exact orderOf_pow_dvd k
  have hquot : (p - 1) / orderOf (g ^ k) = Nat.gcd (p - 1) k := by
    rw [orderOf_pow g, hg]
    exact Nat.div_div_self (Nat.gcd_dvd_left _ _) hp1
  rw [eq_comm]
  exact (odd_div_iff_factorization_two_eq (n := p - 1) (d := orderOf (g ^ k)) hp1 hdiv).symm.trans
    (by
      simpa [hquot] using
        (gcd_odd_iff_right_odd_of_left_even hp1 hEven : Odd (Nat.gcd (p - 1) k) ↔ Odd k))

/-- CRT sends the unit corresponding to `a mod pq` to the pair of units modulo `p` and `q`. -/
private lemma crt_units_unitOfCoprime {p q a : ℕ} (hcop : Nat.Coprime a (p * q))
    (hpqcop : Nat.Coprime p q) :
    ((Units.mapEquiv (ZMod.chineseRemainder hpqcop).toMulEquiv).trans
      (@MulEquiv.prodUnits (ZMod p) (ZMod q) _ _))
        (ZMod.unitOfCoprime a hcop)
    =
      (ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_right p q) hcop),
       ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_left q p) hcop)) := by
  apply Prod.ext <;> apply Units.ext
  · change (ZMod.chineseRemainder hpqcop (a : ZMod (p * q))).1 = (a : ZMod p)
    simp
  · change (ZMod.chineseRemainder hpqcop (a : ZMod (p * q))).2 = (a : ZMod q)
    simp

/-- For a coprime residue mod `pq`, failure of Shor's conditions is equivalent to the
component orders having the same 2-adic valuation. -/
private lemma bad_nat_iff_pair_factorization_eq {p q a : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hcop : Nat.Coprime a (p * q)) :
    let up : (ZMod p)ˣ :=
      ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_right p q) hcop)
    let uq : (ZMod q)ˣ :=
      ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_left q p) hcop)
    ¬is_successful_choice a (p * q) ↔
      (orderOf up).factorization 2 = (orderOf uq).factorization 2 := by
  let up : (ZMod p)ˣ :=
    ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_right p q) hcop)
  let uq : (ZMod q)ˣ :=
    ZMod.unitOfCoprime a (Nat.Coprime.of_dvd_right (dvd_mul_left q p) hcop)
  let r := orderOf up
  let s := orderOf uq
  let l := Nat.lcm r s
  have hpqcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hr : orderOf (a : ZMod p) = r := by
    change orderOf ((up : (ZMod p)ˣ) : ZMod p) = r
    simpa [r] using (orderOf_units (y := up))
  have hs : orderOf (a : ZMod q) = s := by
    change orderOf ((uq : (ZMod q)ˣ) : ZMod q) = s
    simpa [s] using (orderOf_units (y := uq))
  have hN : orderOf (a : ZMod (p * q)) = l := by
    simpa [l] using (orderOf_crt_eq_lcm hpqcop a).trans (by rw [hr, hs])
  have hr0 : r ≠ 0 := (orderOf_pos up).ne'
  have hs0 : s ≠ 0 := (orderOf_pos uq).ne'
  have hl0 : l ≠ 0 := Nat.lcm_ne_zero hr0 hs0
  have hl2 : l.factorization 2 = max (r.factorization 2) (s.factorization 2) := by
    simpa [l] using congrArg (fun f => f 2) (Nat.factorization_lcm hr0 hs0)
  constructor
  · intro hbad
    have hbad' := (not_successful_iff a (p * q)).1 hbad
    rcases hbad' with hodd | hneg
    · have hlodd : Odd l := Nat.not_even_iff_odd.mp (by simpa [hN] using hodd)
      have hlzero : l.factorization 2 = 0 := (odd_iff_factorization_two_eq_zero hl0).1 hlodd
      rw [hl2] at hlzero
      have hrzero : r.factorization 2 = 0 := by omega
      have hszero : s.factorization 2 = 0 := by omega
      exact hrzero.trans hszero.symm
    · have hneg' : (a : ZMod (p * q)) ^ (l / 2) = -1 := by simpa [hN] using hneg
      have hpair := (pow_eq_neg_one_crt hpqcop a (l / 2)).1 hneg'
      have hup_ne : up ^ (l / 2) ≠ 1 := by
        intro hup1
        have hpodd := hp.odd_of_ne_two hp2
        haveI : Fact (2 < p) := by
          have hp1 : 1 < p := hp.one_lt
          rcases hpodd with ⟨k, hk⟩
          exact ⟨by omega⟩
        have hEq : (1 : ZMod p) = -1 := by
          calc
            (1 : ZMod p) = ((up ^ (l / 2) : (ZMod p)ˣ) : ZMod p) := by simp [hup1]
            _ = (a : ZMod p) ^ (l / 2) := by simp [up, ZMod.coe_unitOfCoprime]
            _ = -1 := hpair.1
        exact ZMod.neg_one_ne_one hEq.symm
      have huq_ne : uq ^ (l / 2) ≠ 1 := by
        intro huq1
        have hqodd := hq.odd_of_ne_two hq2
        haveI : Fact (2 < q) := by
          have hq1 : 1 < q := hq.one_lt
          rcases hqodd with ⟨k, hk⟩
          exact ⟨by omega⟩
        have hEq : (1 : ZMod q) = -1 := by
          calc
            (1 : ZMod q) = ((uq ^ (l / 2) : (ZMod q)ˣ) : ZMod q) := by simp [huq1]
            _ = (a : ZMod q) ^ (l / 2) := by simp [uq, ZMod.coe_unitOfCoprime]
            _ = -1 := hpair.2
        exact ZMod.neg_one_ne_one hEq.symm
      have hlr_odd : Odd (l / r) := Nat.not_even_iff_odd.mp
        (div_orderOf_odd_of_pow_ne_one (hdvd := Nat.dvd_lcm_left r s) hup_ne)
      have hls_odd : Odd (l / s) := Nat.not_even_iff_odd.mp
        (div_orderOf_odd_of_pow_ne_one (hdvd := Nat.dvd_lcm_right r s) huq_ne)
      have hlr_eq : l.factorization 2 = r.factorization 2 :=
        (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_left r s)).1 hlr_odd
      have hls_eq : l.factorization 2 = s.factorization 2 :=
        (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_right r s)).1 hls_odd
      exact hlr_eq.symm.trans hls_eq
  · intro heq
    have hlr_eq : l.factorization 2 = r.factorization 2 := by
      rw [hl2, heq, max_eq_left le_rfl]
    have hls_eq : l.factorization 2 = s.factorization 2 := by
      rw [hl2, heq, max_eq_right le_rfl]
    have hlr_odd : Odd (l / r) :=
      (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_left r s)).2 hlr_eq
    have hls_odd : Odd (l / s) :=
      (odd_div_iff_factorization_two_eq hl0 (Nat.dvd_lcm_right r s)).2 hls_eq
    by_cases hle : Even l
    · have hr_even : Even r := by
        have : Even (r * (l / r)) := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_lcm_left r s)]
          exact hle
        exact even_of_even_mul_odd this hlr_odd
      have hs_even : Even s := by
        have : Even (s * (l / s)) := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_lcm_right r s)]
          exact hle
        exact even_of_even_mul_odd this hls_odd
      have hpowp : (a : ZMod p) ^ (l / 2) = -1 := by
        simpa [up, ZMod.coe_unitOfCoprime] using
          unit_pow_half_mul_odd_eq_neg_one hp (x := up) (n := l) (Nat.dvd_lcm_left r s) hlr_odd hr_even
      have hpowq : (a : ZMod q) ^ (l / 2) = -1 := by
        simpa [uq, ZMod.coe_unitOfCoprime] using
          unit_pow_half_mul_odd_eq_neg_one hq (x := uq) (n := l) (Nat.dvd_lcm_right r s) hls_odd hs_even
      have hneg : (a : ZMod (p * q)) ^ (l / 2) = -1 :=
        (pow_eq_neg_one_crt hpqcop a (l / 2)).2 ⟨hpowp, hpowq⟩
      exact (not_successful_iff a (p * q)).2 (Or.inr (by simpa [hN] using hneg))
    · exact (not_successful_iff a (p * q)).2 (Or.inl (by simpa [hN] using hle))

/-- Multiplying by a generator of `(ZMod p)ˣ` changes the 2-adic valuation of the order. -/
private lemma order_factorization_two_mul_generator_ne {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    {g u : (ZMod p)ˣ} (hg : orderOf g = p - 1) :
    (orderOf (u * g)).factorization 2 ≠ (orderOf u).factorization 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hgcard : orderOf g = Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card]
    exact hg.trans (ZMod.card_units p).symm
  have htop : Subgroup.zpowers g = ⊤ := by
    exact (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers g)).mp <| by
      rw [Nat.card_zpowers]
      exact hgcard
  have hu_z : u ∈ Subgroup.zpowers g := by
    simp [htop]
  have hu_p : u ∈ Submonoid.powers g := (mem_powers_iff_mem_zpowers).2 hu_z
  rcases (Submonoid.mem_powers_iff u g).1 hu_p with ⟨k, rfl⟩
  set m := (p - 1).factorization 2
  have hk : (orderOf (g ^ k)).factorization 2 = m ↔ Odd k := by
    simpa [m] using order_factorization_two_eq_generator_iff_odd hp hp2 hg k
  have hk1 : (orderOf (g ^ (k + 1))).factorization 2 = m ↔ Odd (k + 1) := by
    simpa [m] using order_factorization_two_eq_generator_iff_odd hp hp2 hg (k + 1)
  intro hEq
  have hEq' : (orderOf (g ^ (k + 1))).factorization 2 = (orderOf (g ^ k)).factorization 2 := by
    simpa [pow_succ] using hEq
  by_cases hodd : Odd k
  · have hold : (orderOf (g ^ k)).factorization 2 = m := hk.mpr hodd
    have hnew : (orderOf (g ^ (k + 1))).factorization 2 = m := hEq'.trans hold
    have hodd' : Odd (k + 1) := hk1.mp hnew
    rcases hodd with ⟨a, ha⟩
    rcases hodd' with ⟨b, hb⟩
    omega
  · have heven : Even k := (Nat.not_odd_iff_even).mp hodd
    have hodd' : Odd (k + 1) := by
      rcases heven with ⟨a, ha⟩
      use a
      omega
    have hnew : (orderOf (g ^ (k + 1))).factorization 2 = m := hk1.mpr hodd'
    have hold : (orderOf (g ^ k)).factorization 2 = m := hEq'.symm.trans hnew
    exact hodd (hk.mp hold)

/-- Among coprime residues mod pq, at most half are unsuccessful for Shor's algorithm.

    Proof strategy (injection via generator multiplication):
    By CRT, (ℤ/pqℤ)* ≅ (ℤ/pℤ)* × (ℤ/qℤ)*. Choose c via CRT with c ≡ g (mod p) where
    g generates (ℤ/pℤ)*, and c ≡ 1 (mod q). Then multiplication by c sends every
    unsuccessful element to a successful one, giving |unsuccessful| ≤ |successful|.

    The key insight: in a cyclic group of even order n with generator g, exactly one of
    {u, u·g} has order dividing n/2 (since u = g^j and j, j+1 have different parities).
    This means multiplying by g always changes the "2-adic type" of an element's order,
    breaking the v₂-matching condition that characterizes unsuccessful elements. -/
private lemma unsuccessful_bound {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    2 * ((Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))).card
    ≤ (p - 1) * (q - 1) := by
  let hpqcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  let φ : (ZMod (p * q))ˣ ≃* ((ZMod p)ˣ × (ZMod q)ˣ) :=
    (Units.mapEquiv (ZMod.chineseRemainder hpqcop).toMulEquiv).trans
      (@MulEquiv.prodUnits (ZMod p) (ZMod q) _ _)
  let badNat :=
    (Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))
  let pairBadPred : ((ZMod p)ˣ × (ZMod q)ˣ) → Prop := fun uv =>
    (orderOf uv.1).factorization 2 = (orderOf uv.2).factorization 2
  let badPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := Finset.univ.filter pairBadPred
  let goodPairs : Finset ((ZMod p)ˣ × (ZMod q)ˣ) := Finset.univ.filter (fun uv => ¬pairBadPred uv)
  let natToPair : ℕ → ((ZMod p)ˣ × (ZMod q)ˣ) := fun a =>
    if hcop : Nat.Coprime a (p * q) then φ (ZMod.unitOfCoprime a hcop) else 1
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ :=
    isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  have hg : orderOf g = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
    exact hg
  let shift : ((ZMod p)ˣ × (ZMod q)ˣ) → ((ZMod p)ˣ × (ZMod q)ˣ) := fun uv => (uv.1 * g, uv.2)
  have h_badPairs_le_goodPairs : badPairs.card ≤ goodPairs.card := by
    apply Finset.card_le_card_of_injOn shift
    · intro uv huv
      have huv_bad : pairBadPred uv := by
        simpa [badPairs] using huv
      change shift uv ∈ Finset.univ.filter (fun uv => ¬pairBadPred uv)
      simp [Finset.mem_filter]
      intro hshift_bad
      exact order_factorization_two_mul_generator_ne hp hp2 hg <|
        hshift_bad.trans huv_bad.symm
    · intro uv _ vw _ hEq
      rcases Prod.mk.inj hEq with ⟨h1, h2⟩
      apply Prod.ext
      · exact mul_right_cancel h1
      · exact h2
  have h_pair_partition :
      badPairs.card + goodPairs.card = (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := by
    simpa [badPairs, goodPairs] using
      (Finset.filter_card_add_filter_neg_card_eq_card pairBadPred
        (s := (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ))))
  have h_badPairs_bound :
      2 * badPairs.card ≤ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := by
    omega
  have h_badNat_le_badPairs : badNat.card ≤ badPairs.card := by
    apply Finset.card_le_card_of_injOn natToPair
    · intro a ha
      change a ∈ (Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q)) at ha
      rw [Finset.mem_filter] at ha
      have hcop : Nat.Coprime a (p * q) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact ha.2.1
      change natToPair a ∈ Finset.univ.filter pairBadPred
      simp [Finset.mem_filter]
      have hnatToPair : natToPair a = φ (ZMod.unitOfCoprime a hcop) := by
        dsimp [natToPair]
        rw [dif_pos hcop]
      rw [hnatToPair, crt_units_unitOfCoprime hcop hpqcop]
      simpa [pairBadPred] using
        (bad_nat_iff_pair_factorization_eq hp hq hpq hp2 hq2 hcop).1 ha.2.2
    · intro a ha b hb hEq
      change a ∈ (Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q)) at ha
      change b ∈ (Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q)) at hb
      rw [Finset.mem_filter] at ha hb
      have hacop : Nat.Coprime a (p * q) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact ha.2.1
      have hbcop : Nat.Coprime b (p * q) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact hb.2.1
      have ha_lt : a < p * q := Finset.mem_range.mp ha.1
      have hb_lt : b < p * q := Finset.mem_range.mp hb.1
      have hnatToPairA : natToPair a = φ (ZMod.unitOfCoprime a hacop) := by
        dsimp [natToPair]
        rw [dif_pos hacop]
      have hnatToPairB : natToPair b = φ (ZMod.unitOfCoprime b hbcop) := by
        dsimp [natToPair]
        rw [dif_pos hbcop]
      have hunit : ZMod.unitOfCoprime a hacop = ZMod.unitOfCoprime b hbcop := by
        apply φ.injective
        calc
          φ (ZMod.unitOfCoprime a hacop) = natToPair a := hnatToPairA.symm
          _ = natToPair b := hEq
          _ = φ (ZMod.unitOfCoprime b hbcop) := hnatToPairB
      have hzmod : (a : ZMod (p * q)) = (b : ZMod (p * q)) := by
        simpa [ZMod.coe_unitOfCoprime] using congrArg (fun u : (ZMod (p * q))ˣ => (u : ZMod (p * q))) hunit
      have hmod := (ZMod.natCast_eq_natCast_iff' a b (p * q)).1 hzmod
      simpa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] using hmod
  have h_pair_card :
      (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card = (p - 1) * (q - 1) := by
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card_units, ZMod.card_units]
  calc
    2 * ((Finset.range (p * q)).filter (fun a =>
        Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))).card
      = 2 * badNat.card := by rfl
    _ ≤ 2 * badPairs.card := Nat.mul_le_mul_left 2 h_badNat_le_badPairs
    _ ≤ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card := h_badPairs_bound
    _ = (p - 1) * (q - 1) := h_pair_card

/-- Core CRT + cyclic counting bound.
    Among all φ(pq) = (p-1)(q-1) coprime residues mod pq, at least half satisfy
    Shor's success conditions. Proved from coprime_count + unsuccessful_bound
    via the partition identity: successful + unsuccessful = total. -/
private lemma crt_counting_bound {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    2 * ((Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ is_successful_choice a (p * q))).card
    ≥ (p - 1) * (q - 1) := by
  -- Let S be the set of coprime residues
  set S := (Finset.range (p * q)).filter (fun a => Nat.gcd a (p * q) = 1) with hS_def
  set T := (p - 1) * (q - 1) with hT_def
  -- Express the successful and unsuccessful filters as sub-filters of S
  have h_succ : (Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ is_successful_choice a (p * q))
    = S.filter (fun a => is_successful_choice a (p * q)) := by
    rw [hS_def]; rw [Finset.filter_filter]
  have h_unsucc : (Finset.range (p * q)).filter (fun a =>
      Nat.gcd a (p * q) = 1 ∧ ¬is_successful_choice a (p * q))
    = S.filter (fun a => ¬is_successful_choice a (p * q)) := by
    rw [hS_def]; rw [Finset.filter_filter]
  -- Partition: successful.card + unsuccessful.card = S.card = T
  have h_card_S : S.card = T := coprime_count hp hq hpq
  have h_partition := Finset.filter_card_add_filter_neg_card_eq_card
    (fun a => is_successful_choice a (p * q)) (s := S)
  -- Get the unsuccessful bound
  have h_unsucc_bound : 2 * (S.filter (fun a => ¬is_successful_choice a (p * q))).card ≤ T := by
    rw [← h_unsucc]; exact unsuccessful_bound hp hq hpq hp2 hq2
  rw [h_succ]
  omega

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
  sorry
