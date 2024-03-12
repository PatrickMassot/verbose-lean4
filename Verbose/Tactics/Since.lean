import Std.Tactic.LabelAttr
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

def sinceObtainTac (newsT : Term) (news_patt : RCasesPatt) (factsT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let newsE ← elabTerm newsT none
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  newGoal.withContext do
  let lemmas : Array Term := (← verboseConfigurationExt.get).anonymousLemmas.map Lean.Name.toTerm
  let factsT : List Term := newFVarsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right))] ++ lemmas.toList
  let p ← mkFreshExprMVar newsE MetavarKind.syntheticOpaque
  let goalAfter ← newGoal.assert default newsE p
  let newerGoals ← try
    Std.Tactic.SolveByElim.solveByElim.processSyntax {} true false factsT [] #[] [p.mvarId!]
  catch _ => throwError "Could not prove:\n {← ppGoal p.mvarId!}"
  unless newerGoals matches [] do
    throwError "Failed to prove this using the provided facts."
  if let Std.Tactic.RCases.RCasesPatt.typed _ (Std.Tactic.RCases.RCasesPatt.one _ name) _ := news_patt then
    let (_fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro name
    replaceMainGoal [goalAfter]
  else
    let (fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro1P
    goalAfter.withContext do
    replaceMainGoal (← Std.Tactic.RCases.rcases #[(none, mkIdent (← fvar.getUserName))] news_patt goalAfter)

def sinceConcludeTac (conclT : Term) (factsT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let conclE ← elabTermEnsuringValue conclT (← getMainTarget)
  let (newGoal, newFVarsT, _newFVars) ← sinceTac factsT
  let newGoal ← newGoal.change conclE
  newGoal.withContext do
  let factsT : List Term := newFVarsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right))]
  -- logInfo s!"State before calling solve_by_elim: {← ppGoal p.mvarId!}"
  let newerGoals ← Std.Tactic.SolveByElim.solveByElim.processSyntax {} true false factsT [] #[] [newGoal]
  -- logInfo "solve_by_elim done"
  unless newerGoals matches [] do
    throwError "Failed to prove this using the provided facts."
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
  -- logInfo s!"State before calling solve_by_elim: {← ppGoal newGoalAfter}"
  let newerGoals ← Std.Tactic.SolveByElim.solveByElim.processSyntax {} true false factsT [] #[] [newGoalAfter]
  -- logInfo "solve_by_elim ok"
  unless newerGoals matches [] do
    throwError "Failed to prove this using the provided facts."
  replaceMainGoal [← p.mvarId!.tryClearMany newFVars]
