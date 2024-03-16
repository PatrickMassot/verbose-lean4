import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Soit₁ " colGt fixDecl : tactic
syntax "Soit " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Soit₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Soit₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Soit₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Soit₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Soit₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Soit₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)


elab_rules : tactic
  | `(tactic| Soit₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Soit₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Soit₁ $decl:fixDecl))


macro_rules
  | `(tactic| Soit $decl:fixDecl) => `(tactic| Soit₁ $decl)

macro_rules
  | `(tactic| Soit $decl:fixDecl $decls:fixDecl*) => `(tactic| Soit₁ $decl; Soit $decls:fixDecl*)


macro_rules
| `(ℕ) => `(Nat)


example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Soit b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Soit (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Soit (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following works
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Soit n
  success_if_fail_with_msg "There is no object to introduce here."
    Soit h
  intro hn
  Soit k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/- FIXME:
The next examples show that name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Soit (n > 0)
  success_if_fail_with_msg ""
    Soit n
  Soit k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Soit n > 0
  success_if_fail_with_msg ""
    Soit n
  Soit k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Soit n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Soit n ∈ A
  trivial
