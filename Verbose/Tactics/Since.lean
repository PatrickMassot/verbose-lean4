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
     if e.hasSyntheticSorry then
       throwAbortCommand
     hyps := hyps.push
       {userName := .mkSimple s!"GivenFact_{i}",
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
TODO: investigate bug with solve_by_elim not using `congrArg` and `congrFun`.
-/
def trySolveByElim (goal : MVarId) (facts : List Term) (backtracking : Bool := false) : MetaM Bool := do
  let facts := facts ++ [⟨mkIdent `congrFun⟩, ⟨mkIdent `congrArg⟩]
  let state ← saveState
  let newerGoals ← try
      Lean.Elab.Tactic.SolveByElim.processSyntax {seConfig with backtracking} true false facts [] #[] [goal]
    catch _ => restoreState state
               return false
  if newerGoals matches [] && (← goal.isAssigned) then
    return true
  else
    restoreState state
    return false

/-- Try to close the given goal by apply the given lemma and discharging
side condition using solve_by_elim with the given facts.
Return whether it succeeds. The tactic state is preserved in case of failure. -/
def tryLemma! (goal : MVarId) (lem : Name) (facts : List Term) : TacticM (Bool) := do
  let state ← saveState
  -- logInfo s!"will try to apply lemma {lem}"
  if let some newGoals ← tryLemma goal lem then
    -- logInfo "lemma applies"
    for newGoal in newGoals do
      -- logInfo "calling solve_by_elim"
      unless ← trySolveByElim newGoal facts do
        restoreState state
        return false
    return true
  else
    restoreState state
    return false

section cc
open Lean Meta Elab Tactic Std

namespace Mathlib.Tactic.CC

namespace CCState

open CCM

/-- Create a congruence closure state object from the given `config` using the given hypotheses in the
current goal. This is variation on `mkUsingHsCore` from Mathlib. -/
def mkUsingGivenCore (config : CCConfig) (hyps : Array FVarId) : MetaM CCState := do
  let (_, c) ← CCM.run (hyps.forM fun fvar => do
    let dcl ← fvar.getDecl
    unless dcl.isImplementationDetail do
      if ← isProp dcl.type then
        CCM.add dcl.type dcl.toExpr) { mkCore config with }
  return c.toCCState

/-- Run the `cc` tactic but using only the provided hypotheses instead of the full local
context. This a variation on `_root_.Lean.MVarId.cc` from Mathlib.-/
def _root_.Lean.MVarId.ccWithHyps (m : MVarId) (hyps : Array FVarId) (cfg : CCConfig := {}) :
    MetaM Unit := do
  let (introsFVars, m) ← m.intros
  m.withContext do
    let s ← CCState.mkUsingGivenCore cfg (hyps ++ introsFVars)
    let t ← m.getType >>= instantiateMVars
    let s ← s.internalize t
    if s.inconsistent then
        let pr ← s.proofForFalse
        mkAppOptM ``False.elim #[t, pr] >>= m.assign
    else
      let tr := Expr.const ``True []
      let b ← s.isEqv t tr
      if b then
        let pr ← s.eqvProof t tr
        mkAppM ``of_eq_true #[pr] >>= m.assign
      else
        let dbg ← getBoolOption `trace.Meta.Tactic.cc.failure false
        if dbg then
          throwError m!"cc tactic failed, equivalence classes: {s}"
        else
          throwError "cc tactic failed"

end CCState
end Mathlib.Tactic.CC

/-- Try to close the current goal using `cc` with the given hypotheses and report
whether it succeeded.
The tactic state is preserved in case of failure.
-/
def tryCC (goal : MVarId) (hyps : Array FVarId) : MetaM Bool := do
  let state ← saveState
  try
    goal.ccWithHyps hyps
  catch _ =>
    restoreState state
    return false
  return true
end cc

register_endpoint couldNotProve (goal : Format) : CoreM String

/-- Try to close the given goal using the given facts and, in order:
* Try solveByElim
* try each anonymous fact splitting lemma, discharging side condition with the given facts (here the fact that is splitted is the goal here)
* try `cc` using the given facts (only). -/
def trySolveByElimAnonFactSplitCC (goal : MVarId) (factsT : Array Term) (factsFVar : Array FVarId) :
    TacticM Unit := goal.withContext do
  let factsT : List Term := factsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right))]
  -- logInfo s!"Will try to prove: {← ppGoal goal}"
  unless ← trySolveByElim goal factsT do
    let mut failed := true
    let lemmas : Array Name := (← verboseConfigurationExt.get).anonymousFactSplittingLemmas
    for lem in lemmas do
      -- logInfo s!"Will now try lemma: {lem}"
      if ← tryLemma! goal lem factsT then
        failed := false
        break
    if failed then
      -- logInfo "Will now try cc"
      unless ← tryCC goal factsFVar do
        throwError ← couldNotProve (← ppGoal goal)

/-- First call `sinceTac` to derive proofs of the given facts `factsT`. Then try to derive the new
fact described by `newsT` by successively:
* try `solve_by_elim` with the given facts and intro and elimination for `And`.
* try each anonymous fact splitting lemma, discharging side condition with the given facts (here the fact that is splitted is `newsT`)
* try `cc` using the given facts (only).
-/
def sinceObtainTac (newsT : Term) (news_patt : RCasesPatt) (factsT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let newsE ← elabTerm newsT none
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  newGoal.withContext do
  let p ← mkFreshExprMVar newsE MetavarKind.syntheticOpaque
  let goalAfter ← newGoal.assert default newsE p
  trySolveByElimAnonFactSplitCC p.mvarId! newFVarsT newFVars
  if let Lean.Elab.Tactic.RCases.RCasesPatt.typed _ (Lean.Elab.Tactic.RCases.RCasesPatt.one _ name) _ := news_patt then
    let (_fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro name
    replaceMainGoal [goalAfter]
  else
    let (fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro1P
    goalAfter.withContext do
    replaceMainGoal (← Lean.Elab.Tactic.RCases.rcases #[(none, mkIdent (← fvar.getUserName))] news_patt goalAfter)

register_endpoint failedProofUsing (goal : Format) : CoreM String

def sinceConcludeTac (conclT : Term) (factsT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let conclE ← elabTermEnsuringValue conclT (← getMainTarget)
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  let newGoal ← newGoal.change conclE
  newGoal.withContext do
  trySolveByElimAnonFactSplitCC newGoal newFVarsT newFVars
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
  let (suffFVarId, newGoalAfter) ← goalAfter.intro name
  trySolveByElimAnonFactSplitCC newGoalAfter (newFVarsT.push (← `($(mkIdent name))))
    (newFVars.push suffFVarId)
  replaceMainGoal [← p.mvarId!.tryClearMany newFVars]
