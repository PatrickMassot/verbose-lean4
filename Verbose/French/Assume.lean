import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Supposons₁ " colGt assumeDecl : tactic
syntax "Supposons " "que"? (colGt assumeDecl)+ : tactic
syntax "Supposons " "par l'absurde " (colGt assumeDecl) : tactic

elab_rules : tactic
  | `(tactic| Supposons₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Supposons₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Supposons₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Supposons₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Supposons $[que]? $decl:assumeDecl) => `(tactic| Supposons₁ $decl)
  | `(tactic| Supposons $[que]? $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Supposons₁ $decl; Supposons $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Supposons par l'absurde $x:ident : $type) => forContradiction x.getId type


example (P Q : Prop) : P → Q → True := by
  Supposons hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Supposons que hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Supposons que hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "There is no assumption to introduce here."
    Supposons n
  intro n
  Supposons H : n > 0
  trivial


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Supposons hP
  Supposons par l'absurde hnQ :¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Supposons hP
  Supposons par l'absurde hnQ : ¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q := by
  Supposons hP
  Supposons par l'absurde hnQ : Q
  exact h hnQ hP
