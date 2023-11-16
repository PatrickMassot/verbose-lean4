import Verbose.Tactics.Lets
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

elab "Let's" " prove by induction" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

macro "Let's" " prove that " stmt:term : tactic =>
`(tactic| show $stmt)

declare_syntax_cat explicitStmt
syntax ": " term : explicitStmt

def toStmt (e : Lean.TSyntax `explicitStmt) : Lean.Term := ⟨e.raw[1]!⟩

elab "Let's" " prove that " witness:term " works" stmt:(explicitStmt)?: tactic => do
  useTac witness (stmt.map toStmt)

example : 1 + 1 = 2 := by
  Let's prove that 2 = 2
  rfl

variable (k : Nat)

example : ∃ k : ℕ, 4 = 2*k := by
  Let's prove that 2 works
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Let's prove that 2 works: 4 = 2*2
  rfl

/-
example : true ∧ true := by
  Let's prove true
  all_goals {trivial}

example (P Q : Prop) (h : P) : P ∨ Q := by
  Let's prove that P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Let's prove that Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Let's prove that 0 = 0
  trivial
  Let's prove that 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Let's prove that 0 = 0
  trivial
  Let's prove that 1 = 1
  trivial

example : true ↔ true := by
  Let's prove that true → true
  all_goals { exact id }

example (h : false) : 2 = 1 := by
  Let's prove it's contradictory
  exact h
 -/
example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Let's prove by induction H : ∀ k, P k
  . exact h₀
  . exact h k hyp_rec
  . exact H 4

/-
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Let's prove by induction H : true
  Let's prove by induction H : ∀ n, P n
  exact h₀
  exact h

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : true := by
  Let's prove by induction H : ∀ k, P k
  exacts [h₀, h, trivial]

example : true := by
  Let's prove by induction H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial
-/

set_option linter.unusedVariables false in
example : true := by
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Let's prove by induction H : true
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Let's prove by induction H : ∀ n : ℤ, true
  trivial
