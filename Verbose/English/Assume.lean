import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Assume₁ " colGt assumeDecl : tactic
syntax "Assume " "that"? (colGt assumeDecl)+ : tactic
syntax "Assume " "for contradiction " (colGt assumeDecl) : tactic

elab_rules : tactic
  | `(tactic| Assume₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Assume₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Assume₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Assume₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Assume $[that]? $decl:assumeDecl) => `(tactic| Assume₁ $decl)
  | `(tactic| Assume $[that]? $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Assume₁ $decl; Assume $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Assume for contradiction $x:ident : $type) => forContradiction x.getId type


example (P Q : Prop) : P → Q → True := by
  Assume hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Assume that hP (hQ : Q)
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


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assume hP
  Assume for contradiction hnQ :¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Assume hP
  Assume for contradiction hnQ : ¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q := by
  Assume hP
  Assume for contradiction hnQ : Q
  exact h hnQ hP
