import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval

-- (Deutsch-Jozsa Algorithm)

-- Define ket0 for n qubits

def basisState {n : ℕ} (bs0 : BitString n) : QState n :=
    fun bs => if bs = bs0 then 1 else 0

def ket0 (n : ℕ) : QState n :=
    basisState (fun _ => Qubit.zero)
