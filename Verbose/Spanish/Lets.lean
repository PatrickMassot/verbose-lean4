import Verbose.Tactics.Lets
import Mathlib.Tactic.Linarith

open Lean

namespace Verbose.Named
scoped elab "Probemos por inducción" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt
end Verbose.Named

namespace Verbose.NameLess
scoped elab "Probemos por inducción que " stmt:term : tactic =>
letsInduct none stmt
end Verbose.NameLess

open Lean Elab Tactic in
macro "Probemos que " stmt:term :tactic =>
`(tactic| first | show $stmt | apply Or.inl; show $stmt | apply Or.inr; show $stmt | fail "No tienes que probar esto. ¿Querías decir, “Primero probemos que”?")

declare_syntax_cat explicitStmtES
syntax ": " term : explicitStmtES

def toStmt (e : Lean.TSyntax `explicitStmtES) : Lean.Term := ⟨e.raw[1]!⟩

elab "Probemos que " witness:term " basta " stmt:(explicitStmtES)?: tactic => do
  useTac witness (stmt.map toStmt)

elab "Primero probemos que " stmt:term : tactic =>
  anonymousSplitLemmaTac stmt

elab "Probemos ahora que " stmt:term : tactic =>
  unblockTac stmt

syntax "Necesitas anunciarlo: Probemos ahora que " term : term

open Lean Parser Term PrettyPrinter Delaborator in
@[delab app.goalBlocker]
def goalBlocker_delab : Delab := whenPPOption Lean.getPPNotation do
  let stx ← SubExpr.withAppArg delab
  `(Necesitas anunciarlo: Probemos ahora que $stx)

macro "Probemos que hay una contradicción" : tactic => `(tactic|exfalso)

implement_endpoint (lang := es) wrongContraposition : CoreM String :=
pure "No es una contraposición del objetivo actual."

elab "Probemos el contrapositivo: " stmt:term : tactic =>
  showContraposeTac stmt

implement_endpoint (lang := es) inductionError : CoreM String :=
pure "La declaración debe empezar con un cuantificador universal (∀) sobre un número natural."

implement_endpoint (lang := es) notWhatIsNeeded : CoreM String :=
pure "No hace falta demostrar esto."

implement_endpoint (lang := es) notWhatIsRequired : CoreM String :=
pure "Esto no se necesita ahora."

setLang es

example : 1 + 1 = 2 := by
  Probemos que 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Probemos que 2 basta
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Probemos que 2 basta: 4 = 2*2
  rfl

example : True ∧ True := by
  Primero probemos que True
  trivial
  Probemos ahora que True
  trivial

example (P Q : Prop) (h : P) : P ∨ Q := by
  Probemos que P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Probemos que Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Primero probemos que 0 = 0
  trivial
  Probemos ahora que 1 = 1
  trivial

example : (0 : ℤ) = 0 ∧ 1 = 1 := by
  Primero probemos que 0 = 0
  trivial
  Probemos ahora que 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Primero probemos que 1 = 1
  trivial
  Probemos ahora que 0 = 0
  trivial

example : True ↔ True := by
  Primero probemos que True → True
  exact id
  Probemos ahora que True → True
  exact id

example (h : False) : 2 = 1 := by
  Probemos que hay una contradicción
  exact h

section
open Verbose.NameLess

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Probemos por inducción que ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

set_option linter.unusedVariables false in
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : True := by
  Probemos por inducción que ∀ k, P k
  exacts [h₀, h, trivial]

end

section
open Verbose.Named

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Probemos por inducción H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : ∀ k, P k := by
  Probemos por inducción H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "La declaración debe empezar con un cuantificador universal (∀) sobre un número natural."
    Probemos por inducción H : true
  Probemos por inducción H : ∀ n, P n
  exact h₀
  exact h

set_option linter.unusedVariables false in
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : True := by
  Probemos por inducción H : ∀ k, P k
  exacts [h₀, h, trivial]

example : True := by
  Probemos por inducción H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial

-- Check free variable is cleared when main goal is the statement proven
-- by induction applied to a free variable.
set_option linter.unusedTactic false in
example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) (N : ℕ) : P N := by
  Probemos por inducción H : ∀ k, P k
  . fail_if_success let x : Nat := N
    exact h₀
  . fail_if_success let x : Nat := N
    intro k hyp_rec
    exact h k hyp_rec

-- Same with an assumption depending on it
set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) (N : ℕ) (hN : Odd N) : P N := by
  Probemos por inducción H : ∀ k, P k
  . fail_if_success let x : Nat := N
    exact h₀
  . fail_if_success let x : Nat := N
    intro k hyp_rec
    exact h k hyp_rec

set_option linter.unusedVariables false in
example : True := by
  success_if_fail_with_msg "La declaración debe empezar con un cuantificador universal (∀) sobre un número natural."
    Probemos por inducción H : true
  success_if_fail_with_msg "La declaración debe empezar con un cuantificador universal (∀) sobre un número natural."
    Probemos por inducción H : ∀ n : ℤ, true
  trivial

end

example (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  constructor
  Primero probemos que P
  exact h.1
  Probemos ahora que Q
  exact h.2

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Probemos el contrapositivo: ¬ Q → ¬ P
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ∃ x, ¬ P x) : (∀ x, P x) → (∃ x, Q x)  := by
  Probemos el contrapositivo: (∀ x, ¬ Q x) → ∃ x, ¬ P x
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ¬ ∀ x, P x) : (∀ x, P x) → (∃ x, Q x)  := by
  Probemos el contrapositivo: (∀ x, ¬ Q x) → ¬ (∀ x, P x)
  exact h

private def foo (P : Nat → Prop) := ∀ x, P x
configureUnfoldableDefs foo

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ¬ ∀ x, P x) : foo P → (∃ x, Q x)  := by
  Probemos el contrapositivo: (∀ x, ¬ Q x) → ¬ (∀ x, P x)
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ∃ x, ¬ P x) : foo P → (∃ x, Q x)  := by
  Probemos el contrapositivo: (∀ x, ¬ Q x) → ∃ x, ¬ P x
  exact h
