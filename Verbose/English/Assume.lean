import Verbose.English.Common
import Verbose.English.Fix

open Lean Elab Tactic

syntax "Assume₁ " colGt assumeDecl : tactic
syntax "Assume " (colGt assumeDecl)+ : tactic
syntax "Assume that " (colGt term) : tactic
syntax "Assume that " (colGt term " and " term) : tactic
syntax "Assume that " (colGt term ", " term " and " term) : tactic
syntax "Assume " "for contradiction " (colGt assumeDecl) : tactic
syntax "Assume " "for contradiction that " (colGt term) : tactic

elab_rules : tactic
  | `(tactic| Assume₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Assume₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Assume₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Assume₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Assume $decl:assumeDecl) => `(tactic| Assume₁ $decl)
  | `(tactic| Assume $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Assume₁ $decl; Assume $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Assume that $t) => withMainContext do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
  | `(tactic| Assume that $t and $s) => withMainContext do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
     let e ← elabTerm s none
     let name ← mk_hyp_name s e
     Assume1 (introduced.typed (mkNullNode #[s]) name s)
  | `(tactic| Assume that $t, $s and $r) => withMainContext do
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
  | `(tactic| Assume for contradiction $x:ident : $type) => forContradiction x.getId type

elab_rules : tactic
  | `(tactic| Assume for contradiction that $t) => withMainContext do
    let e ← elabTerm t none
    let name ← mk_hyp_name t e
    forContradiction name t

example (P : Prop) : P → True := by
  success_if_fail_with_msg "Given term
  True
is not definitionally equal to the expected
  P"
    Assume that True
  Assume that P
  success_if_fail_with_msg "There is no assumption to introduce here."
    Assume that True
  trivial

example (P Q : Prop) : P → Q → True := by
  Assume that P and Q
  trivial

example (P Q R : Prop) : P → Q → R → True := by
  Assume that P, Q and R
  trivial

example (P Q : Prop) : P → Q → True := by
  Assume hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Assume hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Assume hn
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
  Assume hnQ : Q
  exact h hnQ hP

example : ∀ n > 0, n = n := by
  Assume for contradiction H : ∃ n > 0, n ≠ n
  tauto

private def foo_bar (P : Nat → Prop) := ∀ x, P x

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  success_if_fail_with_msg
    "This is not what you should assume for contradiction, even after pushing negations."
    Assume for contradiction H : ∃ x, ¬ P x
  unfold foo_bar
  Assume for contradiction H : ∃ x, ¬ P x
  exact h H

configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  Assume for contradiction H : ∃ x, ¬ P x
  exact h H

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
