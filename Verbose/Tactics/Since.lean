import Verbose.Tactics.Common

open Lean Elab Tactic Meta
open Std Tactic RCases

/-- Given a list of term that are meant to be statements following directly from the
local assumption, create a new goal where each of those statements have a proof in the local
context. The return value is made of the new goal, an array of terms corresponding to those
proofs and the corresponding FVarIds. -/
def sinceTac (factsT : Array Term) : TacticM (MVarId × Array Term × Array FVarId) := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let factsTE : Array (Term × Expr) ← factsT.mapM (fun t ↦ do pure (.mk t, ← elabTerm t none))
  let mut hyps : Array Lean.Meta.Hypothesis := #[]
  let mut i := 0
  for (t, e) in factsTE do
     hyps := hyps.push
       {userName := (`GivenFact).mkNum  i,
            type := e,
            value := (← elabTerm (← `(strongAssumption% $t)) none)}
     i := i + 1
  let (newFVars, newGoal) ← origGoal.assertHypotheses hyps
  newGoal.withContext do
  let newFVarsT : Array Term ← liftM <| newFVars.mapM fun fvar ↦ do let name ← fvar.getUserName; return mkIdent name
  return (newGoal, newFVarsT, newFVars)

def Lean.Name.toTerm (n : Lean.Name) : Term := ⟨mkIdent n⟩

/-- A version of MVarId.apply that takes a term inside of an Expr and return none instead
of failing when the lemma does not apply. The tactic state is preserved in case of failure. -/
def tryLemma (goal : MVarId) (lem : Name) : TacticM (Option (List MVarId)) := do
  let state ← saveState
  goal.withContext do
  let applyGoals ← try
    goal.apply (← elabTermForApply lem.toTerm)
  catch _ =>
    restoreState state
    return none
  return applyGoals

def seConfig : Lean.Meta.SolveByElim.SolveByElimConfig where
  -- maxDepth := 3
  backtracking := false
  exfalso := false
  intro := false
  constructor := false

/-- Try to close the current goal using solve_by_elim with the given facts and report
whether it succeeded.
The tactic state is preserved in case of failure.
-/
def trySolveByElim (goal : MVarId) (facts : List Term) (backtracking : Bool := false) : MetaM Bool := do
  let state ← saveState
  let newerGoals ← try
      Lean.Elab.Tactic.SolveByElim.processSyntax {seConfig with backtracking} true false facts [] #[] [goal]
    catch _ => restoreState state
               return false
  if newerGoals matches [] then
    return true
  else
    restoreState state
    return false

/-- Try to close the given goal by apply the given lemma and discharging
side condition using solve_by_elim with the given facts.
Return whether it succeeds. The tactic state is preserved in case of failure. -/
def tryLemma! (goal : MVarId) (lem : Name) (facts : List Term) : TacticM (Bool) := do
  -- logInfo s!"will try to apply lemma {lem}"
  if let some newGoals ← tryLemma goal lem then
    -- logInfo "lemma applies"
    for newGoal in newGoals do
      -- logInfo "calling solve_by_elim"
      unless ← trySolveByElim newGoal facts do
        return false
    return true
  else
    return false

def sinceObtainTac (newsT : Term) (news_patt : RCasesPatt) (factsT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let newsE ← elabTerm newsT none
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  newGoal.withContext do
  let lemmas : Array Name := (← verboseConfigurationExt.get).anonymousLemmas
  let factsT : List Term := newFVarsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right))]
  let p ← mkFreshExprMVar newsE MetavarKind.syntheticOpaque
  let goalAfter ← newGoal.assert default newsE p
  unless ← trySolveByElim p.mvarId! factsT do
    let mut failed := true
    for lem in lemmas do
      if ← tryLemma! p.mvarId! lem factsT then
        failed := false
        break
    if failed then
      throwError "Could not prove:\n {← ppGoal p.mvarId!}"
  if let Lean.Elab.Tactic.RCases.RCasesPatt.typed _ (Lean.Elab.Tactic.RCases.RCasesPatt.one _ name) _ := news_patt then
    let (_fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro name
    replaceMainGoal [goalAfter]
  else
    let (fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro1P
    goalAfter.withContext do
    replaceMainGoal (← Lean.Elab.Tactic.RCases.rcases #[(none, mkIdent (← fvar.getUserName))] news_patt goalAfter)

def sinceConcludeTac (conclT : Term) (factsT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let conclE ← elabTermEnsuringValue conclT (← getMainTarget)
  let (newGoal, newFVarsT, _newFVars) ← sinceTac factsT
  let newGoal ← newGoal.change conclE
  newGoal.withContext do
  let factsT : List Term := newFVarsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right))]
  unless ← trySolveByElim newGoal factsT do
    throwError "Failed to prove this using the provided facts.\n{← ppGoal newGoal}"
  replaceMainGoal []

def mkConjunction : List Term → MetaM Term
| [] => `(True)
| [x] => pure x
| h::t => do let conj ← mkConjunction t; `($h ∧ $conj)

def sinceSufficesTac (factsT sufficesT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let sufficesConjT ← mkConjunction sufficesT.toList
  let sufficesConjE ← elabTerm sufficesConjT none
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  newGoal.withContext do
  let p ← mkFreshExprMVar sufficesConjE MetavarKind.syntheticOpaque
  let goalAfter ← newGoal.assert default sufficesConjE p
  let name ← goalAfter.getUnusedUserName `SufficientFact
  let (_, newGoalAfter) ← goalAfter.intro name
  let factsT : List Term := newFVarsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right)), (← `($(mkIdent name)))]
  unless ← trySolveByElim newGoalAfter factsT true do
    throwError "Failed to prove this using the provided facts.\n{← ppGoal newGoalAfter}"
  replaceMainGoal [← p.mvarId!.tryClearMany newFVars]
