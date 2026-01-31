import Lean
import Verbose.Infrastructure.Extension
import Verbose.Tactics.Common

open Lean Meta Elab Tactic Mathlib.Tactic

def claim' (orig_goal : MVarId) (hyp_name : Name) (stmt : Expr) : MetaM (MVarId × MVarId × FVarId) := do
  orig_goal.withContext do
    let hole ← mkFreshExprMVar stmt MetavarKind.syntheticOpaque hyp_name
    let (fvar, mainGoal) ← (← orig_goal.assert hyp_name stmt hole).intro1P
    pure (hole.mvarId!, mainGoal, fvar)

/-- Create a new subgoal `hyp_name : stmt` and return `(subGoal, fvar, mainGoal)` where
`subGoal` is the subgoal and `mainGoal` is an updated version of the main goal
having `hyp_name : stmt` in its context as `fvar`. -/
def claim (hyp_name : Name) (stmt : Term) : TacticM Unit := do
  let orig_goal ← getMainGoal
  orig_goal.withContext do
    let stmt_expr ← elabTerm stmt none
    let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
    replaceMainGoal [subGoal, mainGoal]

register_endpoint inductionError : CoreM String

/-- Perform a proof by induction on a natural number. Note that, compared
to the `induction` tactic, in the inductive case the natural number and inductive
hypotheses are reverted to force user to explicit introduce them. -/
def letsInduct (hyp_name? : Option Name) (stmt : Term) : TacticM Unit := do
  let orig_goal ← getMainGoal
  orig_goal.withContext do
  let stmt_expr ← elabTerm stmt none
  let hyp_name ← if let some hyp_name := hyp_name? then
      checkName hyp_name
      pure hyp_name
    else
      mk_hyp_name stmt stmt_expr
  let .forallE bn bt .. := stmt_expr |
    throwError ← inductionError
  if not (← isDefEq bt (mkConst ``Nat)) then
    throwError ← inductionError
  let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
  subGoal.withContext do
    let (n_fvar, newest_goal) ← subGoal.intro1P
    let goals ← newest_goal.induction n_fvar ``Nat.rec #[{varNames := []}, {varNames := [bn, `hyp_rec]}]
    let #[base_subgoal, ind_subgoal] := goals | throwError "Inductive proof failed"
    let (_, ind_case) ← ind_subgoal.mvarId.revert (goals[1]!.fields.map Expr.fvarId!)
    replaceMainGoal [base_subgoal.mvarId, ind_case, mainGoal]
    evalTactic (← `(tactic|
      (simp_rw [Nat.zero_eq]
       swap
       simp_rw [Nat.succ_eq_add_one]
       swap
       try (pick_goal 3
            first|exact $(mkIdent hyp_name) _|exact $(mkIdent hyp_name)))))

def useTac (witness : Term) (stmt? : Option Term) : TacticM Unit := withMainContext do
  runUse false (pure ()) [witness]
  let newGoal ← getMainGoal
  if let some stmt := stmt? then
     let announcedExpr ← elabTermEnsuringValue stmt (← newGoal.getType)
     replaceMainGoal [← newGoal.replaceTargetDefEq announcedExpr]
  else
     replaceMainGoal [newGoal]

register_endpoint notWhatIsNeeded : CoreM String

def orTac (stmt : Term) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  try
    let [newGoal] ← goal.apply (.const ``Or.inl [])
      | throwError ← notWhatIsNeeded
    let goalExpr ← elabTermEnsuringValue stmt (← newGoal.getType)
    replaceMainGoal [← newGoal.replaceTargetDefEq goalExpr]
  catch _ =>
    try
      let [newGoal] ← goal.apply (.const ``Or.inr [])
        | throwError ← notWhatIsNeeded
      let goalExpr ← elabTermEnsuringValue stmt (← newGoal.getType)
      replaceMainGoal [← newGoal.replaceTargetDefEq goalExpr]
    catch _ => throwError ← notWhatIsNeeded


structure goalBlocker (tgt : Prop) where
  prf : tgt

lemma unblock {tgt : Prop} (block : goalBlocker tgt) : tgt := block.prf

def anonymousSplitLemmaTac (stmt : Term) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do

  -- Maybe there are already several goals
  let goals ← getGoals
  if goals.length > 1 then
    try
      let newGoalType ← elabTermEnsuringValue stmt (← goal.getType)
      let newGoal ← goal.change newGoalType
      let mut newOtherGoals : List MVarId := []
      for otherGoal in goals.tail do
        newOtherGoals := newOtherGoals ++ (← otherGoal.apply (.const `unblock []))
      setGoals ([newGoal] ++ newOtherGoals)
      return
    catch _ => pure ()

  let lemmas := (← verboseConfigurationExt.get).anonymousGoalSplittingLemmas
  for lem in lemmas do
    let lemExpr := (← elabTermForApply (mkIdent lem)).getAppFn
    try
      let newGoals ← goal.apply lemExpr
      let goal := newGoals[0]!
      let newGoal ← goal.withContext do
        let newGoalType ← elabTermEnsuringValue stmt (← goal.getType)
        goal.change newGoalType
      let mut newOtherGoals : List MVarId := []
      for otherGoal in newGoals.tail do
        newOtherGoals := newOtherGoals ++ (← otherGoal.apply (.const `unblock []))
      replaceMainGoal ([newGoal] ++ newOtherGoals)
      trace[Verbose.lemmas] lem
      return ()
    catch _ => pure ()
  throwError ← notWhatIsNeeded

register_endpoint notWhatIsRequired : CoreM String

def unblockTac(stmt : Term) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let goalType ← goal.getType
  unless goalType.getAppFn matches .const `goalBlocker .. do
    throwError ← notWhatIsRequired
  try
    let newGoalType ← elabTermEnsuringValue stmt goalType.getAppArgs[0]!
    let [newGoal] ← goal.apply (.const `goalBlocker.mk []) | failure
    replaceMainGoal [← newGoal.change newGoalType]
  catch _ => throwError ← notWhatIsRequired

register_endpoint wrongContraposition : CoreM String

/-- Claim the current main goal can be contraposed to the given statement. -/
def showContraposeTac (newGoalT : Term) : TacticM Unit := withMainContext do
  withTraceNode `Verbose
    (do return s!"{·.emoji} Will contrapose to get the announced statement") do
  let goal ← getMainGoal
  goal.check_can_contrapose
  let newGoals ← goal.apply (.const ``Mathlib.Tactic.Contrapose.contrapose₁ [])
  replaceMainGoal newGoals
  let goal ← getMainGoal
  -- First try a pure contraposition without any unfolding and pushing
  -- to ensure the core case always works.
  let state ← saveState
  try
    let newE ← elabTermEnsuringValue newGoalT (← goal.getType)
    let newGoal ← goal.change newE
    replaceMainGoal [newGoal]
    trace[Verbose] "Pure contraposition worked."
  catch
  | _ =>
    trace[Verbose] "Pure contraposition failed. Will try to push negations."
    state.restore
    let announcedE ← elabTerm newGoalT none
    if announcedE.hasSyntheticSorry then
      throwAbortCommand
    let prf ← mkFreshExprMVar announcedE MetavarKind.syntheticOpaque
    let announcedGoal := prf.mvarId!
    let (fVars, goalAfter) ← goal.assertHypotheses
      #[{ userName := .mkSimple s!"Announced_goal",
              type := announcedE,
             value := prf }]
    try
      sufficesPushNeg goalAfter fVars[0]!
      pushGoal announcedGoal
    catch
    | e =>
      trace[Verbose] e.toMessageData
      state.restore
      throwError (← wrongContraposition)

lemma And.intro' {a b : Prop} (right : b) (left : a) : a ∧ b := ⟨left, right⟩

lemma Iff.intro' {a b : Prop} (mpr : b → a) (mp : a → b) : a ↔ b := ⟨mp, mpr⟩

lemma abs_le_of_le_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

lemma abs_le_of_le_le' {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

/-- Introduction lemmas for `Iff` and `And` allowing to change the introduction order. -/
AnonymousGoalSplittingLemmasList LogicIntros := Iff.intro Iff.intro' And.intro And.intro'

/-- Lemmas proving inequalities on absolute values. -/
AnonymousGoalSplittingLemmasList AbsIntros := abs_le_of_le_le abs_le_of_le_le'

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros
