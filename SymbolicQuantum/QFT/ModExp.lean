import SymbolicQuantum.QFT.Orthogonality
import SymbolicQuantum.QFT.Period

/-
  The modular-exponentiation oracle as a map on bitstrings, and the fact that
  its fibres are exactly the residue classes mod the period.
-/

/-- `x ↦ a ^ x mod N`, with the residue written as an `m`-bit string.
    `N ≤ 2 ^ m` is what makes the residue fit. -/
def modExpFun (a N n m : ℕ) (hN : 0 < N) (hNm : N ≤ 2 ^ m) (x : BitString n) : BitString m :=
  bitStringEquivFin.symm ⟨a ^ x.toNat % N, lt_of_lt_of_le (Nat.mod_lt _ hN) hNm⟩

/-- The oracle collapses exactly the congruences mod the period: the encoding is
    injective, so equal outputs mean equal residues, and finite order turns that
    back into a congruence of exponents. -/
theorem modExpFun_eq_iff_modEq {a N n m r : ℕ} (hN : 0 < N) (hNm : N ≤ 2 ^ m)
    (hr : is_period a r N) (hrpos : 0 < r) (x y : BitString n) :
    modExpFun a N n m hN hNm x = modExpFun a N n m hN hNm y ↔ x.toNat % r = y.toNat % r := by
  rw [modExpFun, modExpFun, Equiv.apply_eq_iff_eq, Fin.mk.injEq,
    ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, Nat.cast_pow,
    pow_eq_iff_modEq_period hr hrpos]
  exact Iff.rfl

/-- The fibre over `modExpFun x₀` is the residue class of `x₀.toNat` mod `r`. -/
theorem modExpFun_fibre {a N n m r : ℕ} (hN : 0 < N) (hNm : N ≤ 2 ^ m)
    (hr : is_period a r N) (hrpos : 0 < r) (x₀ : BitString n) :
    ∀ x : BitString n,
      modExpFun a N n m hN hNm x = modExpFun a N n m hN hNm x₀ ↔ x.toNat % r = x₀.toNat % r :=
  fun x => modExpFun_eq_iff_modEq hN hNm hr hrpos x x₀
