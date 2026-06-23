import Verbose.Spanish.Common
import Verbose.Spanish.Fix

open Lean Elab Tactic

setLang es

syntax "Supongamos₁ " colGt assumeDecl : tactic
elab_rules : tactic
  | `(tactic| Supongamos₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Supongamos₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Supongamos₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Supongamos₁ $decl:assumeDecl))


namespace Verbose.Named
scoped syntax "Supongamos " (colGt assumeDecl)+ : tactic
scoped syntax "Supongamos " ("para una contradicción " <|> "por contradicción ") (colGt assumeDecl) : tactic

scoped macro_rules
  | `(tactic| Supongamos $decl:assumeDecl) => `(tactic| Supongamos₁ $decl)
  | `(tactic| Supongamos $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Supongamos₁ $decl; Supongamos $decls:assumeDecl*)

scoped elab_rules : tactic
  | `(tactic| Supongamos para una contradicción $x:ident : $type) => forContradiction x.getId type

example (P Q : Prop) : P → Q → True := by
  Supongamos hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Supongamos hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Supongamos hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "Aquí no puedes introducir una hipótesis."
    Supongamos n
  intro n
  Supongamos H : n > 0
  trivial


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Supongamos hP
  Supongamos para  una contradicción hnQ :¬ Q
  exact h hnQ hP

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Supongamos hP
  Supongamos para una contradicción hnQ : ¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Supongamos hP
  Supongamos por contradicción hnQ : ¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q := by
  Supongamos hP
  Supongamos hnQ : Q
  exact h hnQ hP

example : ∀ n > 0, n = n := by
  Supongamos para  una contradicción H : ∃ n > 0, n ≠ n
  tauto

private def foo_bar (P : Nat → Prop) := ∀ x, P x

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  success_if_fail_with_msg
    "Para proceder por contradicción, debes suponer la negación del objetivo."
    Supongamos para  una contradicción H : ∃ x, ¬ P x
  unfold foo_bar
  Supongamos para  una contradicción H : ∃ x, ¬ P x
  exact h H

configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ¬ ∃ x, ¬ P x) : foo_bar P := by
  Supongamos para  una contradicción H : ∃ x, ¬ P x
  exact h H

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "El objetivo ya es una negación, proceder por contradicción no cambia nada. En su lugar, puedes asumir directamente 0 = 1."
    Supongamos para  una contradicción h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Supongamos h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Supongamos para  una contradicción h : 0 = 1
  norm_num at h

-- Check type ascriptions are not needed
example : ¬ (2 : ℝ) * -42 = 2 * 42 := by
  Supongamos hyp : 2 * -42 = 2 * 42
  linarith
end Verbose.Named

namespace Verbose.NameLess
syntax "Supongamos que " (colGt term) : tactic
syntax "Supongamos que " (colGt term " yy " term) : tactic
syntax "Supongamos que " (colGt term ", " term " yy " term) : tactic
syntax "Supongamos " ("para una contradicción que " <|> "por contradicción que ") (colGt term) : tactic

elab_rules : tactic
  | `(tactic| Supongamos que $t) => withMainContext do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
  | `(tactic| Supongamos que $t yy $s) => withMainContext do
     let e ← elabTerm t none
     let name ← mk_hyp_name t e
     Assume1 (introduced.typed (mkNullNode #[t]) name t)
     let e ← elabTerm s none
     let name ← mk_hyp_name s e
     Assume1 (introduced.typed (mkNullNode #[s]) name s)
  | `(tactic| Supongamos que $t, $s yy $r) => withMainContext do
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
  | `(tactic| Supongamos para una contradicción que $t) => withMainContext do
    let e ← elabTerm t none
    let name ← mk_hyp_name t e
    forContradiction name t

example : ∀ n > 0, n = n := by
  Supongamos por contradicción que ∃ n > 0, n ≠ n
  tauto

example : ∀ n > 0, n = n := by
  Supongamos para una contradicción que ∃ n > 0, n ≠ n
  tauto

example (P : Prop) : P → True := by
/-   success_if_fail_with_msg "El término
  True
 no es igual por definición a
  P"
    Supongamos que True -/
  Supongamos que P
  success_if_fail_with_msg "Aquí no puedes introducir una hipótesis."
    Supongamos que True
  trivial

example (P Q : Prop) : P → Q → True := by
  Supongamos que P yy Q
  trivial

example (P Q R : Prop) : P → Q → R → True := by
  Supongamos que P, Q yy R
  trivial

end Verbose.NameLess
