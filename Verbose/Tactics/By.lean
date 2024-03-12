import Lean.LabelAttribute
import Verbose.Tactics.Common

open Lean Elab Tactic Meta
open Std Tactic RCases

register_label_attr anonymous_lemma

def destructTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := do
  let orig_goal ← getMainGoal
  orig_goal.withContext do
  for new in news do
    checkName new.1
  let news := Array.toList news
  match news with
  | [(name, stuff)] => do
    let applied_fact_expr : Expr ← elabTerm fact none
    let type ← instantiateMVars (← inferType applied_fact_expr)
    let newTypeExpr ← match stuff with
    | some new => elabTermEnsuringValue new type
    | none => pure type
    let intermediate_goal ← orig_goal.assert name newTypeExpr applied_fact_expr
    let (_, new_goal) ← intermediate_goal.intro1P
    replaceMainGoal [new_goal]
  | news =>
    let news_patt := news.map RCasesPattOfMaybeTypedIdent
    let new_goals ← rcases #[(none, fact)] (RCasesPatt.tuple Syntax.missing news_patt) (← getMainGoal)
    replaceMainGoal new_goals
    withMainContext do
    let mut goal ← getMainGoal
    for new in news do
      let decl ← getLocalDeclFromUserName new.1
      if let some type := new.2 then
        let actualType ← instantiateMVars (← elabTermEnsuringValue type decl.type)
        goal ← goal.changeLocalDecl decl.fvarId actualType
    replaceMainGoal (goal::new_goals)

def anonymousLemmaTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := do
  let lemmas ←  Lean.labelled `anonymous_lemma
  for lem in lemmas do
    let appStx : Term ← `($(mkIdent lem) $fact)
    try
      destructTac appStx news
      return
    catch _ => pure ()
  throwError "Cannot get this."

def obtainTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := do
  try
    destructTac fact news
  catch
    | e@(.error _ msg) =>
       if (← msg.toString).startsWith "The name" then
         throw e
       else
         anonymousLemmaTac fact news
    | internal => throw internal

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
  let newGoals ← mainGoal.apply (← elabTermForApply fact)
  if newGoals.length != goals.size then
    throwError "Applying this leads to {newGoals.length} goals, not {goals.size}."
  let mut newerGoals : Array MVarId := #[]
  for (goal, announced) in newGoals.zip goals.toList do
    let announcedExpr ← elabTermEnsuringValue announced (← goal.getType)
    newerGoals := newerGoals.push (← goal.replaceTargetDefEq announcedExpr)
  replaceMainGoal newerGoals.toList
