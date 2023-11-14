import Lean
import Verbose.Tactics.Common

open Lean Meta Elab Tactic

def claim' (orig_goal : MVarId) (hyp_name : Name) (stmt : Expr) : MetaM (MVarId × MVarId × FVarId) := do
  orig_goal.withContext do
    let hole ← mkFreshExprMVar stmt MetavarKind.syntheticOpaque hyp_name
    let (fvar, mainGoal) ← (← orig_goal.assert hyp_name stmt hole).intro1P
    pure (hole.mvarId!, mainGoal, fvar)

/-- Create a new subgoal `hyp_name : stmt` and return `(subGoal, fvar, mainGoal)` where
`subGoal` is the subgoal and `mainGoal` is an updated version of the main goal
having `hyp_name : stmt` in its context as `fvar`. -/
def claim (hyp_name : Name) (stmt : Term) : TacticM Unit := do
  let orig_goal ← getMainGoal
  orig_goal.withContext do
    let stmt_expr ← elabTerm stmt none
    let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
    replaceMainGoal [subGoal, mainGoal]

def letsInduct (hyp_name : Name) (stmt : Term) : TacticM Unit := do
  checkName hyp_name
  let orig_goal ← getMainGoal
  orig_goal.withContext do
    let stmt_expr ← elabTerm stmt none
    let .forallE bn bt .. := stmt_expr |
      throwError "The statement must start with a universal quantifier on a natural number."
    if not (← isDefEq bt (mkConst ``Nat)) then
      throwError "The statement must start with a universal quantifier on a natural number."
    let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
    subGoal.withContext do
      let (n_fvar, newest_goal) ← subGoal.intro1P
      let goals ← newest_goal.induction n_fvar ``Nat.rec #[{varNames := []}, {varNames := [bn, `hyp_rec]}]
      replaceMainGoal (((goals.map (·.mvarId))).push mainGoal).toList
