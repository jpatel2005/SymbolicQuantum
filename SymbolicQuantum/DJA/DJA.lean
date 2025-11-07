import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import SymbolicQuantum.QuantumStates
import SymbolicQuantum.QuantumEval

open QGate QCircuit

-- (Deutsch-Jozsa Algorithm)

def basis_state {n : ℕ} (bs0 : BitString n) : QState n :=
    fun bs => if bs = bs0 then 1 else 0

def ket0n (n : ℕ) : QState n :=
    basis_state (fun _ => Qubit.zero)

def H_init (n : ℕ) : QCircuit n :=
    List.foldl (fun acc q => (acc ≫ app (H q))) skip (List.finRange n)

def H_post (n : ℕ) : QCircuit n :=
    List.foldl (fun acc q => (acc ≫ app (H q))) skip (List.finRange n)

def F (n : ℕ) : BitString n -> Bool :=
    fun bs => if bs = (fun _ => Qubit.zero) then true else false

def oracle_block (n : ℕ) (f : BitString (n+1) -> Bool) : QCircuit (n+1) :=
    app (Uf f (Fin.last n))

-- might need to define n as ≥2 (or else the definition of deutsch_jozsa doesn't make sense - also induction will be more intutive this way???)
def deutsch_jozsa (n : ℕ) (f : BitString (n+1) -> Bool) : QCircuit (n+1) :=
    H_init (n+1) ≫
    oracle_block n f ≫
    H_post (n+1)

-- #eval (deutsch_jozsa (3 : ℕ) F)

#print QState
#print BitString
-- QState is (Fin n -> Qubit) -> ℂ
#check QCircuit
