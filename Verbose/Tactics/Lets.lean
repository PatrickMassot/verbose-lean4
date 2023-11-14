import Lean
import Verbose.Common

open Lean Parser Meta Elab Tactic Option

def claim' (orig_goal : MVarId) (hyp_name : Name) (stmt : Expr) : MetaM (MVarId × MVarId × FVarId) := do
  withMVarContext orig_goal do
    let hole ← mkFreshExprMVar stmt MetavarKind.syntheticOpaque hyp_name
    let (fvar, mainGoal) ← intro1P (← assert orig_goal hyp_name stmt hole)
    pure (hole.mvarId!, mainGoal, fvar)

/-- Create a new subgoal `hyp_name : stmt` and return `(subGoal, fvar, mainGoal)` where 
`subGoal` is the subgoal and `mainGoal` is an updated version of the main goal
having `hyp_name : stmt` in its context as `fvar`. -/
def claim (hyp_name : Name) (stmt : Term) : TacticM Unit := do
  let orig_goal ← getMainGoal
  withMVarContext orig_goal do
    let stmt_expr ← elabTerm stmt none
    let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
    replaceMainGoal [subGoal, mainGoal]

elab "my_have" name:ident ":" stmt:term : tactic => do
let _ ← claim name.getId stmt
pure ()

example : 1 = 1 := by
  my_have H : 1 = 1
  . rfl
  exact H


def letsInduct (hyp_name : Name) (stmt : Term) : TacticM Unit := do
  checkName hyp_name
  let orig_goal ← getMainGoal
  withMVarContext orig_goal do
    let stmt_expr ← elabTerm stmt none
    let .forallE bn bt .. := stmt_expr | 
      throwError "The statement must start with a universal quantifier on a natural number."
    if not (← isDefEq bt (mkConst ``Nat)) then
      throwError "The statement must start with a universal quantifier on a natural number."
    let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
    withMVarContext subGoal do
      let (n_fvar, newest_goal) ← intro1P subGoal
      let goals ← Lean.Meta.induction newest_goal n_fvar ``Nat.rec #[{varNames := []}, {varNames := [bn, `hyp_rec]}]
      replaceMainGoal (((goals.map (·.mvarId))).push mainGoal).toList   


elab "Let's" "prove by induction" name:ident ":" stmt:term : tactic => 
letsInduct name.getId stmt

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Let's prove by induction H : ∀ k, P k
  . exact h₀
  . exact h k hyp_rec
  . exact H 4
