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

-- requires the extended binder import
#check ∀ n ≥ 2, true

#check ∃ n ≥ 2, true

example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Fix b (a ≥ 2)
  trivial
