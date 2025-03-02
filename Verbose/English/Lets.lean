import Verbose.Tactics.Lets
import Mathlib.Tactic.Linarith

elab "Let's" " prove by induction" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

open Lean

open Lean Elab Tactic in

macro "Let's" " prove that " stmt:term :tactic =>
`(tactic| first | show $stmt | apply Or.inl; show $stmt | apply Or.inr; show $stmt | fail "This is not what needs to be proven. Did you mean “Let's first prove that”?")

declare_syntax_cat explicitStmtEN
syntax ": " term : explicitStmtEN

def toStmt (e : Lean.TSyntax `explicitStmtEN) : Lean.Term := ⟨e.raw[1]!⟩

elab "Let's" " prove that " witness:term " works" stmt:(explicitStmtEN)?: tactic => do
  useTac witness (stmt.map toStmt)

elab "Let's" " first prove that " stmt:term : tactic =>
  anonymousSplitLemmaTac stmt

elab "Let's" " now prove that " stmt:term : tactic =>
  unblockTac stmt

syntax "You need to announce: Let's now prove that " term : term

open Lean Parser Term PrettyPrinter Delaborator in
@[delab app.goalBlocker]
def goalBlocker_delab : Delab := whenPPOption Lean.getPPNotation do
  let stx ← SubExpr.withAppArg delab
  `(You need to announce: Let's now prove that $stx)

macro "Let's" " prove it's contradictory" : tactic => `(tactic|exfalso)

implement_endpoint (lang := fr) wrongContraposition : CoreM String :=
pure "This is not the contrapositive of the current goal."

elab "Let's prove the contrapositive: " stmt:term : tactic =>
  showContraposeTac stmt

implement_endpoint (lang := en) inductionError : CoreM String :=
pure "The statement must start with a universal quantifier on a natural number."

implement_endpoint (lang := en) notWhatIsNeeded : CoreM String :=
pure "This is not what needs to be proven."

implement_endpoint (lang := en) notWhatIsRequired : CoreM String :=
pure "This is not what is required now."

example : 1 + 1 = 2 := by
  Let's prove that 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Let's prove that 2 works
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Let's prove that 2 works: 4 = 2*2
  rfl

example : True ∧ True := by
  Let's first prove that True
  trivial
  Let's now prove that True
  trivial

example (P Q : Prop) (h : P) : P ∨ Q := by
  Let's prove that P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Let's prove that Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Let's first prove that 0 = 0
  trivial
  Let's now prove that 1 = 1
  trivial

example : (0 : ℤ) = 0 ∧ 1 = 1 := by
  Let's first prove that 0 = 0
  trivial
  Let's now prove that 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Let's first prove that 1 = 1
  trivial
  Let's now prove that 0 = 0
  trivial

example : True ↔ True := by
  Let's first prove that True → True
  exact id
  Let's now prove that True → True
  exact id

example (h : False) : 2 = 1 := by
  Let's prove it's contradictory
  exact h

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Let's prove by induction H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : ∀ k, P k := by
  Let's prove by induction H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Let's prove by induction H : true
  Let's prove by induction H : ∀ n, P n
  exact h₀
  exact h

set_option linter.unusedVariables false in
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : True := by
  Let's prove by induction H : ∀ k, P k
  exacts [h₀, h, trivial]

example : True := by
  Let's prove by induction H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial

set_option linter.unusedVariables false in
example : True := by
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Let's prove by induction H : true
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Let's prove by induction H : ∀ n : ℤ, true
  trivial

example (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  constructor
  Let's first prove that P
  exact h.1
  Let's now prove that Q
  exact h.2

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Let's prove the contrapositive: ¬ Q → ¬ P
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ∃ x, ¬ P x) : (∀ x, P x) → (∃ x, Q x)  := by
  Let's prove the contrapositive: (∀ x, ¬ Q x) → ∃ x, ¬ P x
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ¬ ∀ x, P x) : (∀ x, P x) → (∃ x, Q x)  := by
  Let's prove the contrapositive: (∀ x, ¬ Q x) → ¬ (∀ x, P x)
  exact h

private def foo (P : Nat → Prop) := ∀ x, P x
configureUnfoldableDefs foo

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ¬ ∀ x, P x) : foo P → (∃ x, Q x)  := by
  Let's prove the contrapositive: (∀ x, ¬ Q x) → ¬ (∀ x, P x)
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ∃ x, ¬ P x) : foo P → (∃ x, Q x)  := by
  Let's prove the contrapositive: (∀ x, ¬ Q x) → ∃ x, ¬ P x
  exact h
