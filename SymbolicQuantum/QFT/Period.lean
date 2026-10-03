import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import SymbolicQuantum.Shor.Defs

/-
  The fibre structure behind Shor: the exponents sending `a` to a given value
  form one residue class mod the order, so the inner sum in the QFT amplitude
  is a geometric series.
-/

/-- Two exponents give the same power exactly when they agree mod the period.
    Finite order is needed: in `ZMod 4`, `2 ^ 2 = 2 ^ 3` but `2 ≢ 3`. -/
theorem pow_eq_iff_modEq_period {N : ℕ} {a : ℕ} {r : ℕ} (hr : is_period a r N) (hrpos : 0 < r)
    (x y : ℕ) : ((a : ZMod N) ^ x = (a : ZMod N) ^ y) ↔ x ≡ y [MOD r] := by
  unfold is_period at hr
  have hfin : IsOfFinOrder (a : ZMod N) := orderOf_pos_iff.mp (by rw [hr]; exact hrpos)
  rw [← hr]
  exact hfin.pow_eq_pow_iff_modEq

/-- The fibre of `x ↦ a ^ x` over `a ^ x₀`, inside `range M`, is the set of
    exponents congruent to `x₀` mod the period. -/
theorem fibre_eq_filter_modEq {N : ℕ} {a r : ℕ} (hr : is_period a r N) (hrpos : 0 < r)
    (M x₀ : ℕ) :
    (Finset.range M).filter (fun x => (a : ZMod N) ^ x = (a : ZMod N) ^ x₀)
      = (Finset.range M).filter (fun x => x % r = x₀ % r) := by
  apply Finset.filter_congr
  intro x _
  rw [pow_eq_iff_modEq_period hr hrpos]
  exact Iff.rfl

/-- Reindexing a residue class as an arithmetic progression: the exponents below
    `M` congruent to `x₀` mod `r` are exactly `x₀ % r + j * r` for `j` below the
    number of such terms. -/
theorem mem_filter_modEq_iff {M x₀ r : ℕ} (x : ℕ) :
    (x ∈ (Finset.range M).filter (fun x => x % r = x₀ % r))
      ↔ (∃ j : ℕ, x = x₀ % r + j * r ∧ x < M) := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hxM, hmod⟩
    refine ⟨x / r, ?_, hxM⟩
    conv_lhs => rw [← Nat.div_add_mod x r]
    rw [hmod]
    ring
  · rintro ⟨j, rfl, hlt⟩
    refine ⟨hlt, ?_⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_mod_of_dvd _ dvd_rfl]
