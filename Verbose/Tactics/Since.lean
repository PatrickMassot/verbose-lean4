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
       { userName := .mkSimple s!"GivenFact_{i}",
             type := e,
            value := (← elabTerm (← `(strongAssumption% $t)) none) }
     i := i + 1
  let (newFVars, newGoal) ← origGoal.assertHypotheses hyps
  newGoal.withContext do
  let newFVarsT : Array Term ← liftM <| newFVars.mapM fun fvar ↦ do let name ← fvar.getUserName; return mkIdent name
  return (newGoal, newFVarsT, newFVars)

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
    catch e =>
      trace[Verbose] m!"solve_by_elim failed with {e.toMessageData}"
      restoreState state
      return false
  if newerGoals matches [] && (← goal.isAssigned) then
    return true
  else
    if newerGoals matches [] then
      trace[Verbose] m!"solve_by_elim failed because goal mvar is not assigned."
    else
      trace[Verbose] m!"solve_by_elim failed because there are side goals:\n{← newerGoals.mapM ppGoal}"
    restoreState state
    return false

/-- Try to prove the goal using `solve_by_elim` with the introduction and elimination rules of
`And` in addition to the given facts. Report succes and preserves state in case of failure. -/
def trySolveByElim! (goal : MVarId) (facts : List Term) (backtracking : Bool := false) : MetaM Bool :=   trySolveByElim goal
    (facts ++ [⟨mkIdent `And.intro⟩, ⟨mkIdent `And.left⟩, ⟨mkIdent `And.right⟩]) backtracking

/-- Try to close the goal using the assumption tactic.
Report succes and preserves state in case of failure. -/
def tryAssumption (goal : MVarId) : MetaM (Bool) := goal.withContext do
  trace[Verbose] s!"\nTry assumption on\n{← ppGoal goal}"
  let state ← saveState
  try
    goal.assumption
    return true
  catch
  | _ =>
    restoreState state
    return false

/-- Try to close the given goal by apply the given lemma and discharging
side condition using solve_by_elim with the given facts.
Return whether it succeeds. The tactic state is preserved in case of failure. -/
def tryLemma! (goal : MVarId) (lem : Name) (facts : List Term) (useAssumption : Bool := false) : TacticM (Bool) := do
  trace[Verbose] s!"will try to apply lemma {lem}"
  let state ← saveState
  if let some newGoals ← tryLemma goal lem then
    trace[Verbose] "lemma applies"
    for newGoal in newGoals do
      trace[Verbose] s!"Handling side goal\n{← ppGoal newGoal}"
      if ← newGoal.isAssigned then
        trace[Verbose] "This side goal is already solved"
        continue
      let mut failed := true
      if useAssumption then
        trace[Verbose] "will try to discharge side goal using assumption"
        if (← tryAssumption newGoal) then
          trace[Verbose] "Managed assumption discharging"
          failed := false
      if failed then
        trace[Verbose] s!"will try to discharge side goal using solve_by_elim with {facts}"
        unless ← trySolveByElim newGoal facts do
          restoreState state
          trace[Verbose] s!"could not apply lemma {lem}"
          return false
    trace[Verbose] "lemma successfully applied"
    return true
  else
    restoreState state
    trace[Verbose] s!"could not apply lemma {lem}"
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

/-- Try to close the current goal using `cc` with the given hypotheses and report
whether it succeeded. If the goal is an inequality, try to prove the corresponding equality
using `cc` with the given hypotheses and report whether it succeeded.
The tactic state is preserved in case of failure.
-/
def tryCC! (goal : MVarId) (hyps : Array FVarId) : TacticM Bool := do
  if ← tryCC goal hyps then
    trace[Verbose] "cc worked"
    return true
  else
    trace[Verbose] "Try to use `le_of_eq`"
    let state ← saveState
    let names ← liftMetaM <| hyps.mapM FVarId.getUserName
    if let some [newGoal] ← tryLemma goal ``le_of_eq then
      trace[Verbose] "le_of_eq applies. Will try to prove equality using cc"
      let newHyps ← liftMetaM <| names.mapM getLocalDeclFromUserName
      if ← tryCC newGoal (newHyps.map LocalDecl.fvarId) then
        trace[Verbose] "le_of_eq applied"
        return true
      else
        trace[Verbose] "le_of_eq failed"
        restoreState state
        return false
    else
      restoreState state
      return false
end cc

/-- Try closing the given goal using the `rel` tactic with given proofs,
and report success or failure. Preserves state in case of failure. -/
def tryRel (g : MVarId) (hyps : Array Term) : TacticM Bool := do
  -- Most code is lifted from the `rel` elab in Mathlib.
  let state ← saveState
  g.withContext do
  let hyps ← hyps.mapM (elabTerm · none)
  let .app (.app _rel lhs) rhs ← withReducible g.getType'
    | do
        trace[Verbose] "rel failed, goal not a relation"
        restoreState state
        return false
  unless ← isDefEq (← inferType lhs) (← inferType rhs) do
    trace[Verbose]  "rel failed, goal not a relation"
    restoreState state
    return false
  -- The core tactic `Lean.MVarId.gcongr` will be run with main-goal discharger being the tactic
  -- consisting of running `Lean.MVarId.gcongrForward` (trying a term together with limited
  -- forward-reasoning on that term) on each of the listed terms.
  let assum (g : MVarId) := g.gcongrForward hyps
  -- Time to actually run the core tactic `Lean.MVarId.gcongr`!
  let (_, _, unsolvedGoalStates) ← g.gcongr none [] (mainGoalDischarger := assum)
  match unsolvedGoalStates.toList with
  -- if all goals are solved, succeed!
  | [] => return true
  -- if not, fail and report the unsolved goals
  | unsolvedGoalStates => do
    let unsolvedGoals ← @List.mapM MetaM _ _ _ MVarId.getType unsolvedGoalStates
    let g := Lean.MessageData.joinSep (unsolvedGoals.map Lean.MessageData.ofExpr) Format.line
    trace[Verbose] "rel failed, cannot prove goal by 'substituting' the listed relationships. \
      The steps which could not be automatically justified were:\n{g}"
    restoreState state
    return false

open Linarith in
/-- Try to close the given goal using the given facts and, in order:
* Try solveByElim
* try each anonymous fact splitting lemma, discharging side condition with the given facts (here the fact that is splitted is the goal here)
* try `cc` using the given facts (only)
* try `linarith` using the given fact (only) if there is only one fact (otherwise it’s too powerful)
* try `rel` using the given facts.
-/
def trySolveByElimAnonFactSplitCClinRel (goal : MVarId) (factsT : Array Term) (factsFVar : Array FVarId) :
    TacticM Unit := goal.withContext do
  let factsT' : List Term := factsT.toList
  trace[Verbose] s!"Will try to prove:\n{← ppGoal goal}"
  trace[Verbose] s!"First try solve_by_elim with {factsT'}"
  if ← trySolveByElim goal factsT' then return
  trace[Verbose] s!"Will now try anonymous lemmas"
  let lemmas : Array Name := (← verboseConfigurationExt.get).anonymousFactSplittingLemmas
  for lem in lemmas do
    if ← tryLemma! goal lem factsT' then return
  trace[Verbose] "Will now try cc"
  if ← tryCC! goal factsFVar then
    return
  if factsT.size == 1 then
    let prf : Expr := .fvar factsFVar[0]!
    trace[Verbose] "Will now try linarith"
    try
      linarith true [prf] {preprocessors := defaultPreprocessors, splitNe := true} goal
      return
    catch
      | _ => pure ()
  trace[Verbose] "Will now try rel with {factsT} and goal\n{← ppGoal goal}"
  if ← tryRel goal factsT then
    return
  trace[Verbose] s!"First try solve_by_elim with {factsT'} and And rules"
  if ← trySolveByElim! goal factsT' then return
  throwError ← couldNotProve (← ppGoal goal)

/-- First call `sinceTac` to derive proofs of the given facts `factsT`. Then try to derive the new
fact described by `newsT` by successively:
* try `solve_by_elim` with the given facts and intro and elimination for `And`.
* try each anonymous fact splitting lemma, discharging side condition with the given facts (here the fact that is splitted is `newsT`)
* try `cc` using the given facts (only).
* try `linarith` using the given fact (only) if there is only one fact (otherwise it’s too powerful).
* try `rel` using the given facts (only).
-/
def sinceObtainTac (newsT : Term) (news_patt : RCasesPatt) (factsT : Array Term) : TacticM Unit := do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let newsE ← elabTerm newsT none
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  newGoal.withContext do
  let p ← mkFreshExprMVar newsE MetavarKind.syntheticOpaque
  let goalAfter ← newGoal.assert default newsE p
  trySolveByElimAnonFactSplitCClinRel p.mvarId! newFVarsT newFVars
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
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  let newGoal ← newGoal.change conclE
  newGoal.withContext do
  trySolveByElimAnonFactSplitCClinRel newGoal newFVarsT newFVars
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
  trySolveByElimAnonFactSplitCClinRel newGoalAfter (newFVarsT.push (← `($(mkIdent name))))
    (newFVars.push suffFVarId)
  replaceMainGoal [← p.mvarId!.tryClearMany newFVars]

/-- Establish `factL ∨ factR` and use `Or.elim` on this. The fact is established
using the anonymous case split lemmas or the assumption tactic. Side goals to those
lemmas are aslo handled using the assumption tactic.

TODO: handle also an optional third fact, to allow using `lt_trichotomy` for instance. -/
def sinceDiscussTac (factL factR : Term) : TacticM Unit := withMainContext do
  let origGoal ← getMainGoal
  let disj ← `($factL ∨ $factR)
  let disjE ← elabTerm disj none
  let p ← mkFreshExprMVar disjE MetavarKind.syntheticOpaque
  let goalWithDisj ← origGoal.assert default disjE p
  let lemmas : Array Name := (← verboseConfigurationExt.get).anonymousCaseSplittingLemmas
  unless ← tryAssumption p.mvarId! do
    let mut failed := true
    for lem in lemmas do
      if ← tryLemma! p.mvarId! lem [] true then
        failed := false
        break
    if failed then
      throwError ← couldNotProve (← ppGoal p.mvarId!)
  let name ← goalWithDisj.getUnusedUserName `DisjFact
  let (_disjFVarId, goalAfter) ← goalWithDisj.intro name
  replaceMainGoal [goalAfter]

  evalApplyLikeTactic MVarId.apply <| ← `(Or.elim $(mkIdent name))

  let newGoals ← getGoals
  let goalL := newGoals[0]!
  let newGoalL ← goalL.withContext do
    let disjFVarId ← getFVarFromUserName name
    goalL.tryClear disjFVarId.fvarId!
  let goalR := newGoals[1]!
  let newGoalR ← goalR.withContext do
    let disjFVarId ← getFVarFromUserName name
    goalR.tryClear disjFVarId.fvarId!
  replaceMainGoal [newGoalL, newGoalR]

