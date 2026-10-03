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
