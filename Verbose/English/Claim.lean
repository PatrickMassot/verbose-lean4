import Verbose.Tactics.Lets

open Lean

elab "Claim" name:ident ":" stmt:term : tactic => do
let _ ← claim name.getId stmt

elab "Fact" name:ident ":" stmt:term : tactic => do
let _ ← claim name.getId stmt

example : 1 = 1 := by
  Claim H : 1 = 1
  . rfl
  exact H

/-
example (n : ℕ) : n + n + n = 3*n := by
  Fact key : n + n = 2*n
  by ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fact key : 0 < 2*n by h
  success_if_fail_with_msg ""
    Fact key : 0 < 2*n by h
  Fact keybis : 0 < 2*n by mul_pos applied to [zero_lt_two, h]
  trivial

example (n : ℕ) (h : 0 < n) : 0 < 2*n := by
  Fact key : 0 < 2*n by h
  exact key
-/
