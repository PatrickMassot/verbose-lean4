import Verbose.Tactics.Since
import Verbose.Tactics.We

namespace Lean.Elab.Tactic
open Meta Verbose

open Linarith in
def tryLinarithOnly (goal : MVarId) (facts : List Term) : TacticM Bool := do
  let state ← saveState
  goal.withContext do
  let factsE ← facts.mapM (elabTerm ·.raw none)
  try
    linarith true factsE {preprocessors := defaultPreprocessors} goal
    return true
  catch _ =>
    restoreState state
    return false

register_endpoint failProvingFacts (goal : Format) : CoreM String

def sinceConcludeCalcTac (facts : Array Term) : TacticM Unit := do
  let (newGoal, newFVarsT, newFVars) ← sinceTac facts
  newGoal.withContext do
  if ← trySolveByElim newGoal newFVarsT.toList  then
    -- dbg_trace "solve by elim succeeded"
    return
  else if ← tryLinarithOnly newGoal newFVarsT.toList then
    -- dbg_trace "linarith succeeded"
    return
  else if ← tryCC newGoal newFVars then
    -- dbg_trace "cc succeeded"
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

def fromRelCalcTac (prfs : Array Term) : TacticM Unit := do
  -- logInfo s!"Running fromRelCalcTact with {prf}"
  evalTactic (← `(tactic| rel [$prfs,*]))

def fromCalcTac (prfs : Array Term) : TacticM Unit := do
  if let #[prf] := prfs then
    concludeTac prf <|> fromRelCalcTac #[prf]
  else
    fromRelCalcTac prfs

elab "fromCalcTac" prfs:term,* : tactic => fromCalcTac prfs
