import Verbose.Tactics.Since
import Verbose.Tactics.We

namespace Lean.Elab.Tactic
open Meta Verbose

open Linarith in
def tryLinarithOnly (goal : MVarId) (facts : List Term) : TacticM Bool := do
  let state ← saveState
  goal.withContext do
  let factsE ← facts.mapM (elabTerm · none)
  try
    linarith true factsE {preprocessors := defaultPreprocessors} goal
    return true
  catch _ =>
    restoreState state
    return false

register_endpoint failProvingFacts (goal : Format) : CoreM String

def sinceConcludeCalcTac (facts : Array Term) : TacticM Unit := do
  let (newGoal, newFVarsT, _newFVars) ← sinceTac facts
  newGoal.withContext do
  let factsT : List Term := newFVarsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right))]
  if ← trySolveByElim newGoal factsT then
    return
  else if ← tryLinarithOnly newGoal newFVarsT.toList then
    return
  else
    throwError ← failProvingFacts (← Meta.ppGoal newGoal)

def sinceRelCalcTac (facts : Array Term) : TacticM Unit := do
  -- logInfo s!"Running sinceRelCalcTact with {← liftM <| facts.mapM PrettyPrinter.ppTerm}"
  let (newGoal, newFVarsT, _newFVars) ← sinceTac facts
  newGoal.withContext do
  -- logInfo s!"Context after running sinceTac is\n {← Meta.ppGoal newGoal}"
  -- logInfo s!"fvars passed to gcongrForward are\n {← liftM <| newFVars.mapM FVarId.getUserName}"
  replaceMainGoal [newGoal]
  evalTactic (← `(tactic|rel [$newFVarsT,*]))

def sinceCalcTac (facts : Array Term) : TacticM Unit := do
  sinceConcludeCalcTac facts <|> sinceRelCalcTac facts

def fromRelCalcTac (prf : Term) : TacticM Unit := do
  -- logInfo s!"Running fromRelCalcTact with {prf}"
  evalTactic (← `(tactic| rel [$prf]))

def fromCalcTac (prf : Term) : TacticM Unit := do
  concludeTac prf <|> fromRelCalcTac prf

elab "fromCalcTac" prf:term : tactic => fromCalcTac prf
