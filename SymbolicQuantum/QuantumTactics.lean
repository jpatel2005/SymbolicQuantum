import Lean
import Lean.Elab.Tactic
import SymbolicQuantum.QuantumEval

open Lean Elab Tactic Meta
open Lean.Parser.Tactic

syntax "qseq" (term)? : tactic

macro_rules
  | `(tactic| qseq $thm:term) => `(tactic|
      first
        | apply seq_skip_left
        | apply $thm
        | (
            symm
            apply $thm
          )
        | (
            apply seq_congr_right
            qseq $thm
          )
        | (
            try intro _
            repeat rw [← seq_assoc]
            apply seq_congr_left
            qseq $thm
          )
        | (
            try intro _
            repeat rw [seq_assoc]
            apply seq_congr_right
            qseq $thm
          )
        | (
            try intro _
            repeat rw [seq_assoc]
            apply $thm
          )
        | skip
    )

syntax "qchain" term,+ : tactic

macro_rules
  | `(tactic| qchain $t) => `(tactic| exact $t)
  | `(tactic| qchain $t, $rest,*) => `(tactic|
      refine equiv_trans $t ?_; qchain $rest,*)

syntax "qsimp" (simpArgs)? : tactic

macro_rules
| `(tactic| qsimp) => `(tactic| qsimp [])
| `(tactic| qsimp [$lemmas,*]) => `(tactic| (
  (try simp [mul_comm ((↑√2)⁻¹ : ℂ), ←mul_assoc, mul_add, mul_sub, $lemmas,*]);
  (try ring_nf);
  (try simp [$lemmas,*]);
))
