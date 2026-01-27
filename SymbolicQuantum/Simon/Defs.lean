import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval
import SymbolicQuantum.QuantumDefs

open QGate QCircuit

-- (Simon's Algorithm Definitions)

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

def bxor (q1 q2 : Qubit) : Qubit :=
  match q1, q2 with
  | Qubit.zero, Qubit.zero => Qubit.zero
  | Qubit.zero, Qubit.one  => Qubit.one
  | Qubit.one,  Qubit.zero => Qubit.one
  | Qubit.one,  Qubit.one  => Qubit.zero

def dot_product {n : ℕ} (a b : BitString n) : Qubit :=
  (List.finRange n).foldl (fun acc i =>
    let bit_a := a i
    let bit_b := b i
    match acc, bit_a, bit_b with
    | Qubit.zero, Qubit.one, Qubit.one => Qubit.one
    | Qubit.one,  Qubit.one, Qubit.one => Qubit.zero
    | _, _, _ => acc
  ) Qubit.zero

-- Probability of observing 'y' in the first n qubits
noncomputable def prob_measure_y {n m : ℕ} (ψ : QState (n + m)) (y : BitString n) : ℝ :=
  ∑ z : BitString m, Complex.normSq (ψ (fun i =>
    if h : i < n then
      y ⟨i, h⟩
    else
      z ⟨i - n, by omega⟩
  ))

-- f(x) = f(z) ↔ (x = z) ∨ (x = z ⊕ s)
def simons_promise {n m : ℕ} (f : BitString n → BitString m) (s : BitString n) :=
  ∀ x z, f x = f z ↔
    (x = z ∨ (∀ i, x i = bxor (z i) (s i)))
