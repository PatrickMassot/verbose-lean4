import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Fix₁ " colGt fixDecl : tactic
syntax "Fix " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)


elab_rules : tactic
  | `(tactic| Fix₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Fix₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Fix₁ $decl:fixDecl))


macro_rules
  | `(tactic| Fix $decl:fixDecl) => `(tactic| Fix₁ $decl)

macro_rules
  | `(tactic| Fix $decl:fixDecl $decls:fixDecl*) => `(tactic| Fix₁ $decl; Fix $decls:fixDecl*)


macro_rules
| `(ℕ) => `(Nat)


example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Fix b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Fix (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Fix (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following works
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Fix n
  success_if_fail_with_msg "There is no object to introduce here."
    Fix h
  intro hn
  Fix k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/-
The next examples show that name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Fix (n > 0)
  success_if_fail_with_msg ""
    Fix n
  Fix k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Fix n > 0
  success_if_fail_with_msg ""
    Fix n
  Fix k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Fix n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Fix n ∈ A
  trivial
