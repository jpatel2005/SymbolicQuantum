import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval

open QGate QCircuit

-- left state. forces (right) bits [k...n-1] to be zero
def mask_right {n : ℕ} (k : ℕ) (bs : BitString n) : BitString n :=
  fun i =>
    if i < k then
      bs i
    else
      Qubit.zero

-- right state. forces (left) bits [0...k-1] to be zero
def mask_left {n : ℕ} (k : ℕ) (bs : BitString n) : BitString n :=
  fun i =>
    if i < k then
      Qubit.zero
    else
      bs i

-- top-down
-- combines two states of size n at position k
def tensor_product {n : ℕ} (k_fin : Fin (n+1)) (ψL : QState n) (ψR : QState n) : QState n :=
  let k := k_fin.val
  fun bs =>
    (ψL (mask_right k bs)) * (ψR (mask_left k bs))

notation ψL " ⊗[" k "] " ψR => tensor_product k ψL ψR

def basis_state {n : ℕ} (bs0 : BitString n) : QState n :=
  fun bs => if bs = bs0 then 1 else 0

def ket0 : QState 1 :=
  basis_state (fun _ => Qubit.zero)

def ket1 : QState 1 :=
  basis_state (fun _ => Qubit.one)

noncomputable def ketP : QState 1 :=
  fun (bs : BitString 1) =>
    let coeff := (1 / Real.sqrt 2 : ℂ)
    match bs 0 with
    | Qubit.zero => coeff
    | Qubit.one  => coeff

noncomputable def ketM : QState 1 :=
  fun (bs : BitString 1) =>
    let coeff := (1 / Real.sqrt 2 : ℂ)
    match bs 0 with
    | Qubit.zero => coeff
    | Qubit.one  => -coeff

def ket0n (n : ℕ) : QState n :=
  basis_state (fun _ => Qubit.zero)

noncomputable def ketPn (n : ℕ) : QState n :=
  fun _ => (1 / Real.sqrt (2 ^ n) : ℂ)

-- Lifts a state of size n into n+1 (relevant indices are 0 to n-1)
def embed_prefix {n : ℕ} (ψ : QState n) : QState (n + 1) :=
  fun bs =>
    ψ (fun i => bs ⟨i, by omega⟩)

-- Lifts a state of size 1 into size n+1 (relevant index is n)
def embed_last {n : ℕ} (ψ : QState 1) : QState (n + 1) :=
  fun bs =>
    ψ (fun _ => bs ⟨n, by omega⟩)

-- Lifts a state of size m into size n+m (relevant indices are n to n+m-1)
def embed_suffix {n m : ℕ} (ψ : QState m) : QState (n + m) :=
  fun bs =>
    ψ (fun i => bs ⟨n + i, by omega⟩)

-- Lifts a state of size n into size m (relevant indices are 0 to n-1)
def embed_arb {n m : ℕ} (h : m ≥ n) (ψ : QState n) : QState m :=
  fun bs =>
    ψ (fun i => bs ⟨i, by omega⟩)

-- Lifts a bitstring of size n into size m+1 by appending 0's at the end
def embed_arb_zero {n m : ℕ} (x : BitString n) : BitString (m + 1) :=
  fun i =>
    if h : i < n then
      x ⟨i, h⟩
    else
      Qubit.zero

-- |0...0⟩ ⊗ |-⟩
noncomputable def ket0n_M (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ket0n n)
  let right_part := embed_last ketM
  left_part ⊗[⟨n, by omega⟩] right_part

-- |0...0⟩ ⊗ |1⟩
noncomputable def ket0n_1 (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ket0n n)
  let right_part := embed_last ket1
  left_part ⊗[⟨n, by omega⟩] right_part

-- |0...0⟩ ⊗ |0...0⟩
-- (n zeros) (m zeros)
noncomputable def ket0n_0m (n m : ℕ) : QState (n+m) :=
  let left_part := embed_arb (by omega) (ket0n n)
  let right_part := embed_suffix (ket0n m)
  left_part ⊗[⟨n, by omega⟩] right_part

-- |+...+⟩ ⊗ |0...0⟩
-- (n pluses) (m zeros)
noncomputable def ketPn_0m (n m : ℕ) : QState (n+m) :=
  let left_part := embed_arb (by omega) (ketPn n)
  let right_part := embed_suffix (ket0n m)
  left_part ⊗[⟨n, by omega⟩] right_part

-- |+...+⟩ ⊗ |->
noncomputable def ketPn_M (n : ℕ) : QState (n + 1) :=
  let left_part := embed_prefix (ketPn n)
  let right_part := embed_last ketM
  left_part ⊗[⟨n, by omega⟩] right_part


def QRange_H (n start count : ℕ) : QCircuit n :=
  match count with
  | 0 => skip
  | k + 1 =>
    QRange_H n start k ≫
    if h : (start + k) < n then
      app (H ⟨start + k, h⟩)
    else
      skip

/- MATH DEFS -/

def bxor (q1 q2 : Qubit) : Qubit :=
  match q1, q2 with
  | Qubit.zero, Qubit.zero => Qubit.zero
  | Qubit.zero, Qubit.one  => Qubit.one
  | Qubit.one,  Qubit.zero => Qubit.one
  | Qubit.one,  Qubit.one  => Qubit.zero

def band : Qubit → Qubit → Qubit
| Qubit.one, Qubit.one => Qubit.one
| _, _ => Qubit.zero

def bs_xor {n : ℕ} (a b : BitString n) : BitString n :=
  fun i => bxor (a i) (b i)

def dot_product {n : ℕ} (a b : BitString n) : Qubit :=
  match n with
  | 0 => Qubit.zero
  | n + 1 =>
    let head := band (a 0) (b 0)
    let tail_a := fun (i : Fin n) => a i.succ
    let tail_b := fun (i : Fin n) => b i.succ
    bxor head (dot_product tail_a tail_b)

/-
def dot_product {n : ℕ} (a b : BitString n) : Qubit :=
  (List.finRange n).foldl (fun acc i =>
    let bit_a := a i
    let bit_b := b i
    match acc, bit_a, bit_b with
    | Qubit.zero, Qubit.one, Qubit.one => Qubit.one
    | Qubit.one,  Qubit.one, Qubit.one => Qubit.zero
    | _, _, _ => acc
  ) Qubit.zero
-/
