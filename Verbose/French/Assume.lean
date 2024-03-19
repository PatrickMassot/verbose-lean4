import Verbose.French.Fix

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

setLang fr

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
  success_if_fail_with_msg "Il n’y a pas d’hypothèse à introduire ici."
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
  Supposons hnQ : Q
  exact h hnQ hP

example : ∀ n > 0, n = n := by
  Supposons par l'absurde H : ∃ n > 0, n ≠ n
  tauto

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "Le but est déjà une négation, le démontrer par l’absurde n’apporte rien. Vous pouvez directement supposer 0 = 1."
    Supposons par l'absurde h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Supposons h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Supposons par l'absurde h : 0 = 1
  norm_num at h
