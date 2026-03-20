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
