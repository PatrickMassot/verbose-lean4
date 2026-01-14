import Verbose.French.Common
import Verbose.French.Fix

open Lean Elab Tactic

syntax "Supposons₁ " colGt assumeDecl : tactic
syntax "Supposons " (colGt assumeDecl)+ : tactic
syntax "Supposons que " (colGt term) : tactic
syntax "Supposons que " (colGt term " et " term) : tactic
syntax "Supposons que " (colGt term ", " term " et " term) : tactic
syntax "Supposons " "par l'absurde " (colGt assumeDecl) : tactic
syntax "Supposons " "par l'absurde que " (colGt term) : tactic

elab_rules : tactic
  | `(tactic| Supposons₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Supposons₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Supposons₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Supposons₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Supposons $decl:assumeDecl) => `(tactic| Supposons₁ $decl)
  | `(tactic| Supposons $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Supposons₁ $decl; Supposons $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Supposons que $t) => do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
  | `(tactic| Supposons que $t et $s) => do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
     let e ← elabTerm s none
     let name ← mk_hyp_name s e
     Assume1 (introduced.typed (mkNullNode #[s]) name s)
  | `(tactic| Supposons que $t, $s et $r) => do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
     let e ← elabTerm s none
     let name ← mk_hyp_name s e
     Assume1 (introduced.typed (mkNullNode #[s]) name s)
     let e ← elabTerm r none
     let name ← mk_hyp_name r e
     Assume1 (introduced.typed (mkNullNode #[r]) name r)

elab_rules : tactic
  | `(tactic| Supposons par l'absurde $x:ident : $type) => forContradiction x.getId type

elab_rules : tactic
  | `(tactic| Supposons par l'absurde que $t) => do
    let e ← elabTerm t none
    let name ← mk_hyp_name t e
    forContradiction name t

setLang fr

example (P : Prop) : P → True := by
  success_if_fail_with_msg "L’expression fournie
  True
n’est pas égale par définition à celle attendue
  P"
    Supposons que True
  Supposons que P
  success_if_fail_with_msg "Il n’y a pas d’hypothèse à introduire ici."
    Supposons que True
  trivial

example (P Q : Prop) : P → Q → True := by
  Supposons que P et Q
  trivial

example (P Q R : Prop) : P → Q → R → True := by
  Supposons que P, Q et R
  trivial

example (P Q : Prop) : P → Q → True := by
  Supposons hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Supposons hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Supposons hn
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

private def foo_bar (P : Nat → Prop) := ∀ x, P x

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  success_if_fail_with_msg
    "Ceci n’est pas ce qu’il faut supposer par l’absurde, même après avoir poussé la négation."
    Supposons par l'absurde H : ∃ x, ¬ P x
  unfold foo_bar
  Supposons par l'absurde H : ∃ x, ¬ P x
  exact h H

configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  Supposons par l'absurde H : ∃ x, ¬ P x
  exact h H

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

-- Check type ascriptions are not needed
example : ¬ (2 : ℝ) * -42 = 2 * 42 := by
  Supposons hyp : 2 * -42 = 2 * 42
  linarith
