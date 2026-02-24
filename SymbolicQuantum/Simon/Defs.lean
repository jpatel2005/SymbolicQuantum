import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumDefs

open QGate QCircuit

-- (Simon's Algorithm Definitions)

def combine {n m : ℕ} (ψ : BitString n) (φ : BitString m) : BitString (n + m) :=
  fun i =>
    if h : i < n then
      ψ ⟨i, h⟩
    else
      φ ⟨i - n, by omega⟩

def H_init_simon (n m : ℕ) : QCircuit (n+m) :=
  QRange_H (n+m) 0 n

def H_post_simon (n m : ℕ) : QCircuit (n+m) :=
  QRange_H (n+m) 0 n

def oracle_block_simon (n m : ℕ) (f : BitString n → BitString m) : QCircuit (n+m) :=
  app (Uf_Simon f)

def simon (n m : ℕ) (f : BitString n → BitString m) : QCircuit (n+m) :=
  H_init_simon n m ≫
  oracle_block_simon n m f ≫
  H_post_simon n m

-- Probability of observing 'y' in the first n qubits
noncomputable def prob_measure_y {n m : ℕ} (ψ : QState (n + m)) (y : BitString n) : ℝ :=
  ∑ z : BitString m, Complex.normSq (ψ (fun i =>
    if h : i < n then
      y ⟨i, h⟩
    else
      z ⟨i - n, by omega⟩
  ))

noncomputable def ket_simon (n m : ℕ) (f : BitString n → BitString m) : QState (n + m) :=
  fun bs =>
    let x := fun (i : Fin n) => bs ⟨i, by omega⟩
    let z := fun (i : Fin m) => bs ⟨n + i, by omega⟩
    if z = f x then
      (1 / Real.sqrt (2 ^ n) : ℂ)
    else
      0

-- f(x) = f(z) ↔ (x = z) ∨ (x = z ⊕ s)
def simons_promise {n m : ℕ} (f : BitString n → BitString m) (s : BitString n) :=
  ∀ x z, f x = f z ↔
    (x = z ∨ (∀ i, x i = bxor (z i) (s i)))
