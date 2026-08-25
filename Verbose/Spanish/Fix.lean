import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Sea₁ " colGt fixDecl : tactic
syntax "Sea " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Sea₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Sea₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Sea₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Sea₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Sea₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Sea₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)


elab_rules : tactic
  | `(tactic| Sea₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Sea₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Sea₁ $decl:fixDecl))


macro_rules
  | `(tactic| Sea $decl:fixDecl) => `(tactic| Sea₁ $decl)

macro_rules
  | `(tactic| Sea $decl:fixDecl $decls:fixDecl*) => `(tactic| Sea₁ $decl; Sea $decls:fixDecl*)

implement_endpoint (lang := es) noObjectIntro : CoreM String :=
pure "Aquí no puedes introducir un objeto."

implement_endpoint (lang := es) noHypIntro : CoreM String :=
pure "Aquí no puedes introducir una hipótesis."

implement_endpoint (lang := es) negationByContra (hyp : Format) : CoreM String :=
pure s!"El objetivo ya es una negación, proceder por contradicción no cambia nada. \
 En su lugar, puedes asumir directamente {hyp}."

implement_endpoint (lang := es) wrongNegation : CoreM String :=
pure "Para proceder por contradicción, debes suponer la negación del objetivo."

macro_rules
| `(ℕ) => `(Nat)

setLang es

example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Sea b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sea (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sea (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following works
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sea n
  success_if_fail_with_msg "Aquí no puedes introducir un objeto."
    Sea h
  intro hn
  Sea k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/-
The next examples show that name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Sea (n > 0)
  success_if_fail_with_msg ""
    Sea n
  Sea k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Sea n > 0
  success_if_fail_with_msg ""
    Sea n
  Sea k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Sea n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Sea n ∈ A
  trivial
