import Verbose.Infrastructure.Extension
import Verbose.Tactics.Common

open Lean Elab Tactic Meta
open Std Tactic RCases

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
    let new_goals ← rcases #[(none, fact)] (RCasesPatt.tuple Syntax.missing news_patt) orig_goal
    replaceMainGoal new_goals
    withMainContext do
    let mut goal ← getMainGoal
    for new in news do
      let decl ← goal.withContext do getLocalDeclFromUserName new.1
      if let some type := new.2 then
        let actualType ← goal.withContext do instantiateMVars (← elabTermEnsuringValue type decl.type)
        goal ← goal.changeLocalDecl decl.fvarId actualType
    replaceMainGoal (goal::new_goals)

register_endpoint cannotGet : CoreM String

def anonymousLemmaTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := do
  let lemmas := (← verboseConfigurationExt.get).anonymousFactSplittingLemmas
  for lem in lemmas do
    let appStx : Term ← `($(mkIdent lem) $fact)
    try
      destructTac appStx news
      return
    catch _ => pure ()
  throwError ← cannotGet

register_endpoint theName : CoreM String

def obtainTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := do
  try
    destructTac fact news
  catch
    | e@(.error _ msg) =>
       if (← msg.toString).startsWith (← theName) then
         throw e
       else
         anonymousLemmaTac fact news
    | internal => throw internal

register_endpoint needName : CoreM String

open Mathlib.Tactic.Choose in
def chooseTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit := withMainContext do
  for new in news do
    checkName new.1
  let applied_fact_expr : Expr ← elabTerm fact none
  if news.isEmpty then throwError ← needName
  let new_names := (← news.mapM fun p ↦ (mkBinderIdent p.1)).toList
  let newGoal : MVarId ← elabChoose true (some applied_fact_expr) new_names (.failure []) (← getMainGoal)
  newGoal.withContext do
  let mut newerGoal : MVarId := newGoal
  for new in news[1:] do
    if let (n, some t) := new then
      let decl ← newerGoal.withContext do getLocalDeclFromUserName n
      newerGoal := ← newerGoal.changeLocalDecl decl.fvarId (← elabTerm t none)
  replaceMainGoal [newerGoal]

register_endpoint wrongNbGoals : CoreM String
register_endpoint couldNotInferImplVal (var : Name) : CoreM String
register_endpoint doesNotApply (fact : Format) : CoreM String
register_endpoint alsoNeedCheck (fact : Format) : CoreM String

-- Note: the following tactics try to catch some potentatial user mistakes, but *many*
-- things could go wrong.
def bySufficesTac (fact : Term) (goals : Array Term) : TacticM Unit := do
  let mainGoal ← getMainGoal
  mainGoal.withContext do
  let newGoals ←
    try
      mainGoal.apply (← elabTermForApply fact)
    catch | _ => throwError (← doesNotApply (← PrettyPrinter.ppTerm fact))
  -- logInfo <| s!"Goals after `apply`: {← newGoals.mapM fun g ↦ do ppExpr (← g.getType)}"

  let extraGoals := newGoals.toArray[goals.size:].toArray
  -- logInfo <| s!"Extra goals after `apply`: {← extraGoals.mapM fun g ↦ do ppExpr (← g.getType)}"
  if newGoals.length < goals.size then
    throwError (← wrongNbGoals)
  -- By previous test, we know the zip below won’t silently drop anything announced by user
  let mut newerGoals : Array MVarId := #[]
  for (goal, announced) in newGoals.zip goals.toList do
    let goalType ← goal.getType
    unless ← isProp goalType do
      -- Here we assume the user provided too many statements in the suffices clause
      -- and one such statement is about to be matched with some implicit data goal
      throwError (← couldNotInferImplVal (← goal.getTag))
    let announcedExpr ← elabTermEnsuringValue announced (← goal.getType)
    newerGoals := newerGoals.push (← goal.replaceTargetDefEq announcedExpr)
  -- Since we checked the length of new goal and nothing failed in the above loop,
  -- anything in `extraGoals` is created by apply and should have been unified during
  -- the above loop
  let unassignedGoals : Array MVarId ← extraGoals.filterM fun goal ↦ notM goal.isAssigned
  for goal in unassignedGoals do
    let goalType ← goal.getType
    let ppGoal ← ppExpr goalType
    if ← isProp goalType then
      throwError (← alsoNeedCheck ppGoal)
    else
      throwError (← couldNotInferImplVal (← goal.getTag))
  replaceMainGoal newerGoals.toList

