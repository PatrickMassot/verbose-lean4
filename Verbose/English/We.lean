import Verbose.Tactics.We

open Lean Parser Tactic

/--
We rewrite
-/
macro (name := weRewrite) rw:"We" "rewrite using" s:myRwRuleSeq l:(location)? : tactic =>
  rewrite_macro rw s l

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  We rewrite using ← h at h'
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  We rewrite using [← h] at h'
  exact h'

elab "We" "discuss using" exp:term : tactic =>
  discussOr exp

example (P Q : Prop) (h : P ∨ Q) : True := by
  We discuss using h
  . intro _hP
    trivial
  . intro _hQ
    trivial

elab "We" "discuss depending on" exp:term : tactic =>
  discussEm exp

example (P : Prop) : True := by
  We discuss depending on P
  . intro _hP
    trivial
  . intro _hnP
    trivial
