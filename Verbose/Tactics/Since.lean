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
  withTraceNode `Verbose (fun e ↦ do
    let facts ← liftM <| factsT.mapM PrettyPrinter.ppTerm
    return m!"{e.emoji} Will try to derive facts: {facts}") do
  let factsE : Array Expr ← factsT.mapM (fun t ↦ elabTerm t none)
  let mut hyps : Array Lean.Meta.Hypothesis := #[]
  let mut i := 0
  for e in factsE do
     if e.hasSyntheticSorry then
       throwAbortCommand
     let factGoal ← mkFreshExprMVar e MetavarKind.syntheticOpaque
     strongAssumption factGoal.mvarId!
     hyps := hyps.push
       { userName := .mkSimple s!"GivenFact_{i}",
             type := e,
            value := factGoal }
     i := i + 1
  let (newFVars, newGoal) ← origGoal.assertHypotheses hyps
  newGoal.withContext do
  let newFVarsT : Array Term ← liftM <| newFVars.mapM fun fvar ↦ do let name ← fvar.getUserName; return mkIdent name
  return (newGoal, newFVarsT, newFVars)

/-- Try to close the current goal using solve_by_elim with the given facts and report
whether it succeeded.
The tactic state is preserved in case of failure.
TODO: investigate bug with solve_by_elim not using `congrArg` and `congrFun`.
-/
partial def trySolveByElim (goal : MVarId) (facts : List Term) : MetaM Bool := do
  let facts := facts ++ [⟨mkIdent `congrFun⟩, ⟨mkIdent `congrArg⟩]
  let state ← saveState
  let newerGoals ← try
      Lean.Elab.Tactic.SolveByElim.processSyntax {constructor := false} true false facts [] #[] [goal]
    catch e =>
      trace[Verbose] m!"solve_by_elim failed with message: {e.toMessageData}"
      restoreState state
      if (← whnf (← goal.getType)).isAppOf ``And then
        let [l, r] ← goal.applyConst ``And.intro | do state.restore; return false
        trace[Verbose] m!"Will try solve_by_elim on both sides of the conjunction."
        if (← trySolveByElim l facts) && (← trySolveByElim r facts) then
          return true
        else
          state.restore
          return false
      if (← whnf (← goal.getType)).isAppOf ``Iff then
        let [l, r] ← goal.applyConst ``Iff.intro | do state.restore; return false
        trace[Verbose] m!"Will try solve_by_elim on both implications."
        if (← trySolveByElim l facts) && (← trySolveByElim r facts) then
          return true
        else
          state.restore
          return false
      return false
  let newerGoals ← newerGoals.filterM (fun g ↦ notM g.isAssigned)
  if newerGoals matches [] && (← goal.isAssigned) then
    trace[Verbose] m!"solve_by_elim proved {← goal.getType}."
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
def trySolveByElim! (goal : MVarId) (facts : List Term) : MetaM Bool := trySolveByElim goal
    (facts ++ [⟨mkIdent `And.intro⟩, ⟨mkIdent `And.left⟩, ⟨mkIdent `And.right⟩])

/-- Try to close the goal using the assumption tactic.
Report succes and preserves state in case of failure. -/
def tryAssumption (goal : MVarId) : MetaM (Bool) := goal.withContext do
  withTraceNode `Verbose (do return s!"{·.emoji!} Will try assumption") do
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
  withTraceNode `Verbose (do return s!"{·.emoji!} Will try to apply lemma {lem}") do
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

/-- This function will be used to discharge side goals in rels using the given
expressions hs. We only try to close the goal using each hypothesis. This
is weaker than the default discharger, on purpose, since it does not call
positivity, but it uses solveByElim using the given facts, assuming those facts
are fvarids. -/
def gcongr_side (hs : Array Expr) (g : MVarId) : MetaM Unit :=
  withReducible do
    let s ← saveState
    withTraceNode `Meta.gcongr (fun _ => return m!"gcongr side goal: ⊢ {← g.getType}") do
    -- Iterate over a list of terms
    for h in hs do
      try
        withTraceNode `Meta.gcongr (return m!"{·.emoji} trying {h}") do
          g.assignIfDefeq h
        return
      catch _ => s.restore
    withTraceNode `Meta.gcongr (return m!"{·.emoji} trying solveByElim") do
    if ← trySolveByElim g (← hs.mapM fun h ↦ do return ⟨mkIdent (← h.fvarId!.getUserName)⟩).toList then
      return
    s.restore
    throwError "gcongr_side failed"

open Mathlib.Tactic.GCongr in
/-- A version of _root_.Lean.MVarId.gcongrForward which also tries solveByElim
using the given facts, assuming those facts are fvarids. -/
def _root_.Lean.MVarId.gcongrForwardStrong (hs : Array Expr) (g : MVarId) : MetaM Unit :=
  withReducible do
    let s ← saveState
    withTraceNode `Meta.gcongr (fun _ => return m!"gcongr_forward: ⊢ {← g.getType}") do
    -- Iterate over a list of terms
    let tacs := (forwardExt.getState (← getEnv)).2
    for h in hs do
      try
        tacs.firstM fun (n, tac) =>
          withTraceNode `Meta.gcongr (return m!"{·.emoji} trying {n} on {h} : {← inferType h}") do
            tac.eval h g
        return
      catch _ =>
        s.restore
    withTraceNode `Meta.gcongr (return m!"{·.emoji} trying solveByElim") do
    if ← trySolveByElim g (← hs.mapM fun h ↦ do return ⟨mkIdent (← h.fvarId!.getUserName)⟩).toList then
      return
    s.restore
    throwError "gcongr_forward failed"

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
  let assum (g : MVarId) := g.gcongrForwardStrong hyps
  -- Time to actually run the core tactic `Lean.MVarId.gcongr`!
  let (_, _, unsolvedGoalStates) ← g.gcongr none [] (sideGoalDischarger := gcongr_side hyps)
                                            (mainGoalDischarger := assum)
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

def try_lemmas (lemmas : Array Name) (goal : MVarId) (facts : List Term) : TacticM Bool := do
  for lem in lemmas do
    if ← tryLemma! goal lem facts then
      return true
  return false

open Linarith in
def try_linarith_one_prf (goal : MVarId) (prf : Expr) : TacticM Bool := do
  let state ← saveState
  try
    linarith true [prf] {preprocessors := defaultPreprocessors, splitNe := true} goal
    return true
  catch | _ => state.restore; return false

def trySimpa (g : MVarId) (a b : Term) : TacticM Bool := g.withContext do
  let goals ← getGoals
  let state ← saveState
  setGoals [g]
  try
    evalTactic (← `(tactic| focus simpa only [$a:term] using $b:term))
    setGoals goals
    trace[Verbose] s!"simpa succeeded"
    return true
  catch
  | e =>
    trace[Verbose] e.toMessageData
    state.restore
    setGoals [g]
    try
      evalTactic (← `(tactic| focus simpa only [$b:term] using $a:term))
      trace[Verbose] s!"simpa succeeded"
      setGoals goals
      return true
    catch
      | _ =>
        trace[Verbose] e.toMessageData
        state.restore
        return false

def trySimpOnly (g : MVarId) (hyp : Term) : TacticM Bool := g.withContext do
  let goals ← getGoals
  let state ← saveState
  setGoals [g]
  try
    evalTactic (← `(tactic| focus ((simp only [$hyp:term]; try apply le_rfl); done)))
    setGoals goals
    return true
  catch
  | e =>
    trace[Verbose] e.toMessageData
    state.restore
    return false

def tryAll_core (goal : MVarId) (factsT : Array Term) (factsFVar : Array FVarId) :
    TacticM Unit := goal.withContext do
  let mut factsT' : List Term := factsT.toList
  for fvar in factsFVar do
    unless (← fvar.getType).isAppOf `And do continue
    let ident := mkIdent (← fvar.getUserName)
    let l ← `($(mkIdent `And.left) $ident)
    let r ← `($(mkIdent `And.right) $ident)
    factsT' := l :: r :: factsT'
  if ← factsFVar.anyM hasAnd then
    if ← (withTraceNode `Verbose (fun e ↦ do
        return s!"{emo e} Will now try solve_by_elim with {factsT'} and And rules") do
      trySolveByElim! goal factsT') then return
  else
    if ← (withTraceNode `Verbose (fun e ↦ do return s!"{emo e} Will try solve_by_elim with {factsT'}") do
        trySolveByElim goal factsT') then return
  let lemmas : Array Name := (← verboseConfigurationExt.get).anonymousFactSplittingLemmas
  if ← (withTraceNode `Verbose (fun e ↦ do return s!"{emo e} Will now try anonymous fact splitting lemmas") do
    try_lemmas lemmas goal factsT') then return
  let lemmas : Array Name := (← verboseConfigurationExt.get).anonymousGoalSplittingLemmas
  if ← (withTraceNode `Verbose (fun e ↦ do return s!"{emo e} Will now try anonymous goal splitting lemmas") do
    try_lemmas lemmas goal factsT') then return
  if factsFVar.size == 2 && (← factsFVar.anyM isEqEqv) then
    if ← (withTraceNode `Verbose (fun e ↦ do
        return s!"{emo e} Will now try simpa with {factsT}.") do
      trySimpa goal factsT[0]! factsT[1]!) then return
  if factsFVar.size == 1 && (← isEqEqv factsFVar[0]!) then
    if ← (withTraceNode `Verbose (fun e ↦ do
        return s!"{emo e} Will now try simp only with {factsT[0]!}.") do
      trySimpOnly goal factsT[0]!) then return
  if ← factsFVar.anyM isEqEqv then
    if ← withTraceNode `Verbose (fun e ↦ do return s!"{emo e} Will now try cc") do
      tryCC! goal factsFVar then return
  if factsT.size == 1 then
    let prf : Expr := .fvar factsFVar[0]!
    unless (← factsFVar[0]!.getType).isAppOf `And do
    if ← withTraceNode `Verbose (fun e ↦ do return s!"{emo e} Will now try linarith") do
      try_linarith_one_prf goal prf then return
  if ← withTraceNode `Verbose (fun e ↦ do
      return s!"{emo e} Will now try rel with {factsT}") do
    trace[Verbose] "and goal\n{← ppGoal goal}"
    tryRel goal factsT then return
  let mut used_fvars : FVarIdSet  := (← (← goal.getType).collectFVars.run {}).2.fvarSet
  for fact in factsFVar do
    used_fvars := used_fvars.union (← (← fact.getType).collectFVars.run {}).2.fvarSet
  let cond (decl : LocalDecl) : Bool :=
    used_fvars.contains decl.fvarId || factsFVar.contains decl.fvarId
  throwError ← couldNotProve (← ppGoalFiltered goal cond)
where
  emo : Except Exception Bool → String
    | .ok true => checkEmoji
    | _ => crossEmoji
  isEqEqv (fvar : FVarId) : TacticM Bool := do
    let typ ← fvar.getType
    return typ.isAppOf `Eq || typ.isAppOf `Iff
  hasAnd (fvar : FVarId) : TacticM Bool := do
    let typ ← whnf (← fvar.getType)
    return typ.containsConst (· == `And)


def makeNumbersRelReal {m : Type → Type} [Monad m] [MonadQuotation m] : Term → m (Bool × Term)
| `($a:num = $b:num) => `(($a : ℝ) = $b) >>= go
| `($a:num ≥ $b:num) => `(($a : ℝ) ≥ $b) >>= go
| `($a:num ≤ $b:num) => `(($a : ℝ) ≤ $b) >>= go
| `($a:num > $b:num) => `(($a : ℝ) > $b) >>= go
| `($a:num < $b:num) => `(($a : ℝ) < $b) >>= go
| `($a:num ≠ $b:num) => `(($a : ℝ) ≠ $b) >>= go
| t => return (false, t)
where go (t : Term) : m (Bool × Term) := return (true, t)

register_endpoint unusedFact (fact : String) : TacticM String

/-- Try to close the given goal using the given facts and, in order:
* Try push_neg (if there is exactly one face and either the fact or goal uses `Not`)
* Try solveByElim
* try each anonymous fact splitting lemma, discharging side condition with the given facts (here the fact that is splitted is the goal here)
* try `cc` using the given facts (only) if those facts include an equality or equivalence
* try `linarith` using the given fact (only) if there is only one fact (otherwise it’s too powerful)
* try `rel` using the given facts.
* try `simpa` if there are exactly two facts
* try `simp only` if there is exactly one fact
* Try solveByElim with And rules if at least one fact uses And
-/
def tryAll (goal : MVarId) (factsT : Array Term) (factsFVar : Array FVarId) :
    TacticM Unit := goal.withContext do
  withTraceNode `Verbose (do return s!"{·.emoji} Will try to prove:\n{← ppGoal goal}") do
  let state ← saveState
  if factsT.size == 1 then
    -- This could be a push_neg attempt. We try this first since it should fail quickly.
    let fvar := factsFVar[0]!
    let tgt ← instantiateMVars (← goal.getType)
    let given ← instantiateMVars (← fvar.getType)
    if tgt.getUsedConstants.contains `Not || given.getUsedConstants.contains `Not then
      try
        let origGoals ← getGoals
        sufficesPushNeg goal fvar
        setGoals (← origGoals.filterM (·.isAssigned))
        return
      catch
      | e =>
        trace[Verbose] e.toMessageData
    state.restore
  tryAll_core (goal : MVarId) (factsT : Array Term) (factsFVar : Array FVarId)
  let prf ← instantiateMVars (.mvar goal)
  trace[Verbose] "Found proof: {← ppExpr prf}"
  for fvar in factsFVar do
    if !(prf.containsFVar fvar) then
      let stmt ← fvar.getType
      throwError (← unusedFact <| toString (← PrettyPrinter.ppExpr stmt))
  return

/-- First call `sinceTac` to derive proofs of the given facts `factsT`. Then try to derive the new
fact described by `newsT` using `tryAll` and destruct it using `rcases`.
-/
def sinceObtainTac (newsT : Term) (news_patt : RCasesPatt) (factsT : Array Term) : TacticM Unit := focus do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let state ← saveState
  checkRCasesPattName news_patt
  let newsE ← elabTerm newsT none
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  newGoal.withContext do
  let p ← mkFreshExprMVar newsE MetavarKind.syntheticOpaque
  let goalAfter ←
  try
    let goalAfter ← newGoal.assert default newsE p
    tryAll p.mvarId! newFVarsT newFVars
    pure goalAfter
  catch
  | e => do
    state.restore
    let (mod, newsT) ← makeNumbersRelReal newsT
    let (mods, factsT) := (← factsT.mapM makeNumbersRelReal).unzip
    if mod || mods.any (· matches true) then
      trace[Verbose] "Detected term involving a relation between numeric literals, will try again with numbers in ℝ"
      let newsE ← elabTerm newsT none
      -- TODO reuse proofs found above for facts that did not change?
      let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
      newGoal.withContext do
      let p ← mkFreshExprMVar newsE MetavarKind.syntheticOpaque
      let goalAfter ← newGoal.assert default newsE p
      try
        tryAll p.mvarId! newFVarsT newFVars
        return goalAfter
      catch
      | _ =>
        state.restore
        throw e
    else
      throw e

  if let Lean.Elab.Tactic.RCases.RCasesPatt.typed _ (Lean.Elab.Tactic.RCases.RCasesPatt.one _ name) _ := news_patt then
    let (_fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro name
    replaceMainGoal [goalAfter]
  else
    let (fvar, goalAfter) ← (← goalAfter.tryClearMany newFVars).intro1P
    goalAfter.withContext do
    replaceMainGoal (← Lean.Elab.Tactic.RCases.rcases #[(none, mkIdent (← fvar.getUserName))] news_patt goalAfter)

def sinceConcludeTac (conclT : Term) (factsT : Array Term) : TacticM Unit := focus do
  let origGoal ← getMainGoal
  origGoal.withContext do
  let conclE ← elabTermEnsuringValue conclT (← getMainTarget)
  let state ← saveState
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  let newGoal ← newGoal.change conclE
  newGoal.withContext do
  try
    tryAll newGoal newFVarsT newFVars
  catch
  | e =>
    trace[Verbose] "Got error {e.toMessageData}"
    state.restore
    let (mods, factsT) := (← factsT.mapM makeNumbersRelReal).unzip
    unless mods.any (· matches true) do throw e
    withTraceNode `Verbose
      (do return s!"{·.emoji} Detected term involving a relation between numeric literals, will try again with numbers in ℝ") do
    let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
    let newGoal ← newGoal.change conclE
    newGoal.withContext do
    try
      tryAll newGoal newFVarsT newFVars
    catch
    | e' =>
      trace[Verbose] "Got error {e'.toMessageData}"
      state.restore
      throw e
  unless (← getGoals) matches [] do replaceMainGoal []

def mkConjunction : List Term → MetaM Term
| [] => `(True)
| [x] => pure x
| h::t => do let conj ← mkConjunction t; `($h ∧ $conj)

/-- Establish the statements from `factsT` using `sinceTac` then tries to close
the main goal using those and the statements from `sufficesT` before leaving
the later as new goals. -/
def sinceSufficesTac (factsT sufficesT : Array Term) : TacticM Unit :=
  focus <| withMainContext do
  let state ← saveState
  let mut suffHyps : Array Lean.Meta.Hypothesis := #[]
  let mut suffGoals : List MVarId := []
  let mut i := 0
  for t in sufficesT do
    let e ← elabTerm t none
    if e.hasSyntheticSorry then
      throwAbortCommand
    let prf ← mkFreshExprMVar e MetavarKind.syntheticOpaque
    suffHyps := suffHyps.push
       { userName := .mkSimple s!"SufficientFact_{i}",
             type := e,
            value := prf }
    suffGoals := suffGoals.concat prf.mvarId!
    i := i + 1
  let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
  let (fVars, goalAfter) ← newGoal.assertHypotheses suffHyps
  goalAfter.withContext do
  let suffsT ← fVars.mapM fun fvar ↦ do return mkIdent (← fvar.getUserName)
  try
    tryAll goalAfter (newFVarsT ++ suffsT)
      (newFVars ++ fVars)
    replaceMainGoal suffGoals
  catch
  | e =>
    trace[Verbose] "Got error {e.toMessageData}"
    state.restore
    let (modSs, sufficesT) := (← sufficesT.mapM makeNumbersRelReal).unzip
    let (modFs, factsT) := (← factsT.mapM makeNumbersRelReal).unzip
    unless (modSs ++ modFs).any (· matches true) do throw e
    withTraceNode `Verbose
      (do return s!"{·.emoji} Detected term involving a relation between numeric literals, will try again with numbers in ℝ") do
    let mut suffHyps : Array Lean.Meta.Hypothesis := #[]
    let mut suffGoals : List MVarId := []
    let mut i := 0
    for t in sufficesT do
      let e ← elabTerm t none
      if e.hasSyntheticSorry then
        throwAbortCommand
      let prf ← mkFreshExprMVar e MetavarKind.syntheticOpaque
      suffHyps := suffHyps.push
         { userName := .mkSimple s!"SufficientFact_{i}",
               type := e,
              value := prf }
      suffGoals := suffGoals.concat prf.mvarId!
      i := i + 1
    let (newGoal, newFVarsT, newFVars) ← sinceTac factsT
    let (fVars, goalAfter) ← newGoal.assertHypotheses suffHyps
    goalAfter.withContext do
    let suffsT ← fVars.mapM fun fvar ↦ do return mkIdent (← fvar.getUserName)
    try
      tryAll goalAfter (newFVarsT ++ suffsT)
        (newFVars ++ fVars)
      replaceMainGoal suffGoals
    catch
    | e' =>
      trace[Verbose] "Got error {e'.toMessageData}"
      state.restore
      throw e

def prove_disjunction (goal : MVarId) (lemmas : Array Name) : TacticM Unit := do
  let stmt ← goal.getType
  withTraceNode `Verbose (do return s!"{·.emoji} Will try to prove disjunction {← ppExpr stmt}") do
  unless ← tryAssumption goal do
    let mut failed := true
    for lem in lemmas do
      if ← tryLemma! goal lem [] true then
        failed := false
        break
    if failed then
      throwError ← couldNotProve (← ppGoal goal)

/-- Establish `factL ∨ factR` and use `Or.elim` on this. The fact is established
using the anonymous case split lemmas or the assumption tactic. Side goals to those
lemmas are aslo handled using the assumption tactic.

TODO: handle also an optional third fact, to allow using `lt_trichotomy` for instance. -/
def sinceDiscussTac (factL factR : Term) : TacticM Unit :=
  focus <| withMainContext do
  let origGoal ← getMainGoal
  let disj ← `($factL ∨ $factR)
  let disjE ← elabTerm disj none
  withTraceNode `Verbose (do return s!"{·.emoji} Will try to prove disjunction {← ppExpr disjE} or the other way around") do
  let p ← mkFreshExprMVar disjE MetavarKind.syntheticOpaque
  let goalWithDisj ← origGoal.assert default disjE p
  let lemmas : Array Name := (← verboseConfigurationExt.get).anonymousCaseSplittingLemmas
  let state ← saveState
  try
    prove_disjunction p.mvarId! lemmas
  catch
  | _ => -- We will try the symmetric goal
    state.restore
    let some [symmGoal] ← tryLemma p.mvarId! `Or.symm | throwError "Goal is not an or??"
    prove_disjunction symmGoal lemmas
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

