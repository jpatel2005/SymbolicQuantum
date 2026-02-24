import Mathlib.Data.Real.Sqrt
import SymbolicQuantum.DJA.Defs

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

syntax "qunfold" ("[" ident,* "]")? : tactic

macro_rules
| `(tactic| qunfold [$defs,*]) =>
    `(tactic|
      (
        $[try unfold $defs;]*
        try unfold ketPn_0m;
        try unfold ket0n_0m;
        try unfold ket0n_M;
        try unfold ketPn_M;
        try unfold ketPn;
        try unfold ket0n;
        try unfold tensor_product;
        try unfold mask_left;
        try unfold mask_right;
        try unfold embed_arb;
        try unfold embed_prefix;
        try unfold embed_suffix;
        try unfold embed_last;
        try unfold ketP;
        try unfold ketM;
        try unfold ket0;
        try unfold basis_state;
        try unfold Qubit.toNat;
        try simp
      )
    )
