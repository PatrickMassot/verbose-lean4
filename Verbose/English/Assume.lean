import Verbose.English.Fix

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

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "The goal is a negation, there is no point in proving it by contradiction. You can directly assume 0 = 1."
    Assume for contradiction h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Assume h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Assume for contradiction h : 0 = 1
  norm_num at h

-- Check type ascriptions are not needed
example : ¬ (2 : ℝ) * -42 = 2 * 42 := by
  Assume hyp : 2 * -42 = 2 * 42
  linarith
