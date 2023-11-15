import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Assume₁ " colGt assumeDecl : tactic
syntax "Assume " "that"? (colGt assumeDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Assume₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Assume₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Assume₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Assume₁ $decl:assumeDecl))

-- TODO: find how to merge lines 1 and 2 and lines 3 and 4.
macro_rules
  | `(tactic| Assume $decl:assumeDecl) => `(tactic| Assume₁ $decl)
  | `(tactic| Assume that $decl:assumeDecl) => `(tactic| Assume₁ $decl)
  | `(tactic| Assume $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Assume₁ $decl; Assume $decls:assumeDecl*)
  | `(tactic| Assume that $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Assume₁ $decl; Assume $decls:assumeDecl*)


example (P Q : Prop) : P → Q → True := by
  Assume hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Assume that hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "There is no assumption to introduce here."
    Assume n
  intro n
  Assume H : n > 0
  trivial


/-
Assume for contradiction is missing.

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assume hP
  Assume for contradiction hnQ
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assume hP
  Assume for contradiction hnQ : ¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q := by
  Assume hP
  Assume for contradiction hnQ : Q
  exact h hnQ hP
-/
