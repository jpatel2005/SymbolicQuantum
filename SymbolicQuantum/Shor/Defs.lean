import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumDefs

-- Modular exponentiation
def mod_exp (a x N : ℕ) : ℕ :=
  (a ^ x) % N

-- Definition of period
-- a^r ≡ 1 (mod N) and r is the smallest positive integer that satisfies this
def is_period (a r N : ℕ) : Prop :=
  r > 0 ∧
  mod_exp a r N = 1 ∧
  ∀ k, 0 < k → k < r → mod_exp a k N ≠ 1

-- Complex phase shift used in QFT
noncomputable def qft_phase (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℂ))
