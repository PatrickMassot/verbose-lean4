import Verbose.Tactics.Lets
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

namespace Verbose.French

elab "Montrons" " par récurrence" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

open Lean Elab Tactic in
elab "Montrons" " que " stmt:term : tactic => do
  evalTactic (← `(tactic| show $stmt)) <|> orTac stmt

declare_syntax_cat explicitStmtFR
syntax ": " term : explicitStmtFR

def toStmt (e : Lean.TSyntax `explicitStmtFR) : Lean.Term := ⟨e.raw[1]!⟩

elab "Montrons" " que " witness:term " works" stmt:(explicitStmtFR)?: tactic => do
  useTac witness (stmt.map toStmt)

elab "Montrons" " d'abord que " stmt:term : tactic =>
  anonymousSplitLemmaTac stmt

elab "Montrons" " maintenant que " stmt:term : tactic =>
  unblockTac stmt

syntax "Vous devez annoncer: Montrons maintenant que " term : term

open Lean Parser Term PrettyPrinter Delaborator in
@[delab app.goalBlocker]
def goalBlocker_delab : Delab := whenPPOption Lean.getPPNotation do
  let stx ← SubExpr.withAppArg delab
  `(Vous devez annoncer: Montrons maintenant que $stx)

lemma And.intro' {a b : Prop} (right : b) (left : a) : a ∧ b := ⟨left, right⟩

lemma Iff.intro' {a b : Prop} (mpr : b → a) (mp : a → b) : a ↔ b := ⟨mp, mpr⟩

lemma abs_le_of_le_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

lemma abs_le_of_le_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

attribute [local anonymous_split_lemma] Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

macro "Montrons" " prove it's contradictory" : tactic => `(tactic|exfalso)

example : 1 + 1 = 2 := by
  Montrons que 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Montrons que 2 works
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Montrons que 2 works: 4 = 2*2
  rfl

example : True ∧ True := by
  Montrons d'abord que True
  trivial
  Montrons maintenant que True
  trivial

example (P Q : Prop) (h : P) : P ∨ Q := by
  Montrons que P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Montrons que Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Montrons d'abord que 0 = 0
  trivial
  Montrons maintenant que 1 = 1
  trivial

example : (0 : ℤ) = 0 ∧ 1 = 1 := by
  Montrons d'abord que 0 = 0
  trivial
  Montrons maintenant que 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Montrons d'abord que 1 = 1
  trivial
  Montrons maintenant que 0 = 0
  trivial

example : True ↔ True := by
  Montrons d'abord que True → True
  exact id
  Montrons maintenant que True → True
  exact id

example (h : False) : 2 = 1 := by
  Montrons prove it's contradictory
  exact h

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Montrons par récurrence H : ∀ k, P k
  . exact h₀
  . exact h k hyp_rec
  . exact H 4

/-
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Montrons par récurrence H : true
  Montrons par récurrence H : ∀ n, P n
  exact h₀
  exact h

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : true := by
  Montrons par récurrence H : ∀ k, P k
  exacts [h₀, h, trivial]

example : true := by
  Montrons par récurrence H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial
-/

set_option linter.unusedVariables false in
example : true := by
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Montrons par récurrence H : true
  success_if_fail_with_msg "The statement must start with a universal quantifier on a natural number."
    Montrons par récurrence H : ∀ n : ℤ, true
  trivial
