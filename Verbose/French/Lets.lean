import Verbose.Tactics.Lets
import Mathlib.Tactic.Linarith

namespace Verbose.French

elab "Montrons" " par récurrence" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

open Lean Elab Tactic in

macro "Montrons" " que " stmt:term :tactic =>
`(tactic| first | show $stmt | apply Or.inl; show $stmt | apply Or.inr; show $stmt)

declare_syntax_cat explicitStmtFR
syntax " : " term : explicitStmtFR

def toStmt (e : Lean.TSyntax `explicitStmtFR) : Lean.Term := ⟨e.raw[1]!⟩

elab "Montrons" " que " witness:term " convient" stmt:(explicitStmtFR)?: tactic => do
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

macro "Montrons" " une contradiction" : tactic => `(tactic|exfalso)

open Lean

implement_endpoint (lang := fr) inductionError : CoreM String :=
pure "Le but d’une démonstration par récurrence doit commencer par un quantificateur universel portant sur un entier naturel."

implement_endpoint (lang := fr) notWhatIsNeeded : CoreM String :=
pure "Ce n’est pas ce qu’il faut démontrer."

implement_endpoint (lang := fr) notWhatIsRequired : CoreM String :=
pure "Ce n’est pas ce qui est requis maintenant."

setLang fr

example : 1 + 1 = 2 := by
  Montrons que 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Montrons que 2 convient
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Montrons que 2 convient: 4 = 2*2
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
  Montrons une contradiction
  exact h

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Montrons par récurrence H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "Le but d’une démonstration par récurrence doit commencer par un quantificateur universel portant sur un entier naturel."
    Montrons par récurrence H : true
  Montrons par récurrence H : ∀ n, P n
  exact h₀
  exact h

set_option linter.unusedVariables false in
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : True := by
  Montrons par récurrence H : ∀ k, P k
  exacts [h₀, h, trivial]

example : True := by
  Montrons par récurrence H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial

set_option linter.unusedVariables false in
example : true := by
  success_if_fail_with_msg "Le but d’une démonstration par récurrence doit commencer par un quantificateur universel portant sur un entier naturel."
    Montrons par récurrence H : true
  success_if_fail_with_msg "Le but d’une démonstration par récurrence doit commencer par un quantificateur universel portant sur un entier naturel."
    Montrons par récurrence H : ∀ n : ℤ, true
  trivial
