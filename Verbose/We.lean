import Lean
import Verbose.Common

open Lean Parser Meta Elab Tactic Option

/- Restore rewrite using a single term without brackets. -/
declare_syntax_cat myRwRuleSeq
syntax rwRule : myRwRuleSeq
syntax "[" rwRule,*,? "]" : myRwRuleSeq


/--
We rewrite
-/
macro (name := weRewrite) rw:"We" "rewrite using" c:(config)? s:myRwRuleSeq l:(location)? : tactic =>
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

def discussOr (input : Term) : TacticM Unit := do 
    evalApplyLikeTactic Meta.apply <| ← `(Or.elim $input)

elab "We" "discuss using" exp:term : tactic => 
  discussOr exp

example (P Q : Prop) (h : P ∨ Q) : True := by
  We discuss using h
  . intro _hP
    trivial
  . intro _hQ
    trivial

macro "We" "discuss depending on" exp:term : tactic =>
`(tactic| We discuss using Classical.em $exp) 

example (P : Prop) : True := by
  We discuss depending on P
  . intro _hP
    trivial
  . intro _hnP
    trivial
