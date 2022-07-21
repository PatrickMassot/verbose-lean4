import Lean
import Verbose.Common

open Lean Parser Meta Elab Tactic Option

declare_syntax_cat myRwRuleSeq
syntax rwRule : myRwRuleSeq
syntax "[" rwRule,*,? "]" : myRwRuleSeq


/--
We rewrite
-/
macro (name := rwSeq) rw:"We" "rewrite using" c:(config)? s:myRwRuleSeq l:(location)? : tactic =>
  match s with
  | `(myRwRuleSeq| [%$lbrak $rs:rwRule,* ]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| rewrite%$rw $(c)? [%$lbrak $rs,*] $(l)?; try (with_reducible rfl%$rbrak))
  | `(myRwRuleSeq| $rs:rwRule) =>
    `(tactic| rewrite%$rw $(c)? [$rs] $(l)?; try (with_reducible rfl))
  | _ => Macro.throwUnsupported


example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  We rewrite using ← h at h'
  exact h'

