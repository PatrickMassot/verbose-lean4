import Verbose.Tactics.Common

open Lean Elab Tactic Meta
open Std Tactic RCases


def obtainTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := do
  let orig_goal ← getMainGoal
  orig_goal.withContext do
  for new in news do
    checkName new.1
  let applied_fact_expr : Expr ← elabTerm fact none
  let news := Array.toList news
  match news with
  | [(name, stuff)] => do
    let type ← inferType applied_fact_expr
    if let some new := stuff then
      if not (← isDefEq (← elabTerm new type) type) then throwError "No way"
    let intermediate_goal ← orig_goal.assert name type (← elabTerm fact none)
    let (_, new_goal) ← intermediate_goal.intro1P
    replaceMainGoal [new_goal]
  | news =>
    let news_patt := news.map RCasesPattOfMaybeTypedIdent
    let new_goals ← rcases #[(none, fact)] (RCasesPatt.tuple Syntax.missing news_patt) (← getMainGoal)
    replaceMainGoal new_goals

open Mathlib.Tactic.Choose in
def chooseTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := do
  (← getMainGoal).withContext do
  for new in news do
    checkName new.1
  let applied_fact_expr : Expr ← elabTerm fact none
  if news.isEmpty then throwError "You need to provide a name for the chosen object."
  let new_names := (← news.mapM fun p ↦ (mkBinderIdent p.1)).toList
  let newGoal : MVarId ← elabChoose true (some applied_fact_expr) new_names (.failure []) (← getMainGoal)
  newGoal.withContext do
  let mut newerGoal : MVarId := newGoal
  for new in news[1:] do
    if let (n, some t) := new then
      let decl ← getLocalDeclFromUserName n
      newerGoal := ← newGoal.changeLocalDecl decl.fvarId (← elabTerm t none)
  replaceMainGoal [newerGoal]

def bySufficesTac (fact : Term) (goals : Array Term) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
  let newGoals ← mainGoal.apply (← elabTerm fact none)
  if newGoals.length != goals.size then
    throwError "Applying this leads to {newGoals.length} goals, not {goals.size}."
  let mut newerGoals : Array MVarId := #[]
  for (goal, announced) in newGoals.zip goals.toList do
    let announcedExpr ← elabTermEnsuringValue announced (← goal.getType)
    newerGoals := newerGoals.push (← goal.replaceTargetDefEq announcedExpr)
  replaceMainGoal newerGoals.toList
