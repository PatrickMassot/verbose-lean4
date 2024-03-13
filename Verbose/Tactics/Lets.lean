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

def letsInduct (hyp_name : Name) (stmt : Term) : TacticM Unit := do
  checkName hyp_name
  let orig_goal ← getMainGoal
  orig_goal.withContext do
    let stmt_expr ← elabTerm stmt none
    let .forallE bn bt .. := stmt_expr |
      throwError "The statement must start with a universal quantifier on a natural number."
    if not (← isDefEq bt (mkConst ``Nat)) then
      throwError "The statement must start with a universal quantifier on a natural number."
    let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
    subGoal.withContext do
      let (n_fvar, newest_goal) ← subGoal.intro1P
      let goals ← newest_goal.induction n_fvar ``Nat.rec #[{varNames := []}, {varNames := [bn, `hyp_rec]}]
      replaceMainGoal (((goals.map (·.mvarId))).push mainGoal).toList

def useTac (witness : Term) (stmt? : Option Term) : TacticM Unit := withMainContext do
  runUse false (pure ()) [witness]
  let newGoal ← getMainGoal
  if let some stmt := stmt? then
     let announcedExpr ← elabTermEnsuringValue stmt (← newGoal.getType)
     replaceMainGoal [← newGoal.replaceTargetDefEq announcedExpr]
  else
     replaceMainGoal [newGoal]

def orTac (stmt : Term) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  try
    let [newGoal] ← goal.apply (.const ``Or.inl [])
      | throwError "This is not what needs to be proven."
    let goalExpr ← elabTermEnsuringValue stmt (← newGoal.getType)
    replaceMainGoal [← newGoal.replaceTargetDefEq goalExpr]
  catch _ =>
    try
      let [newGoal] ← goal.apply (.const ``Or.inr [])
        | throwError "This is not what needs to be proven."
      let goalExpr ← elabTermEnsuringValue stmt (← newGoal.getType)
      replaceMainGoal [← newGoal.replaceTargetDefEq goalExpr]
    catch _ => throwError "This is not what needs to be proven."


structure goalBlocker (tgt : Prop) where
  prf : tgt

lemma unblock {tgt : Prop} (block : goalBlocker tgt) : tgt := block.prf

def anonymousSplitLemmaTac (stmt : Term) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let lemmas := (← verboseConfigurationExt.get).anonymousSplitLemmas
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
      return ()
    catch _ => pure ()
  throwError "This is not what needs to be proven."

def unblockTac(stmt : Term) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let goalType ← goal.getType
  unless goalType.getAppFn matches .const `goalBlocker .. do
    throwError "This is not what is required now."
  try
    let newGoalType ← elabTermEnsuringValue stmt goalType.getAppArgs[0]!
    let [newGoal] ← goal.apply (.const `goalBlocker.mk []) | failure
    replaceMainGoal [← newGoal.change newGoalType]
  catch _ => throwError "This is not what is required now."

lemma And.intro' {a b : Prop} (right : b) (left : a) : a ∧ b := ⟨left, right⟩

lemma Iff.intro' {a b : Prop} (mpr : b → a) (mp : a → b) : a ↔ b := ⟨mp, mpr⟩

lemma abs_le_of_le_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

lemma abs_le_of_le_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

/-- Introduction lemmas -/
AnonymousSplitLemmasList LogicIntros := Iff.intro Iff.intro' And.intro And.intro'

AnonymousSplitLemmasList AbsIntros := abs_le_of_le_le abs_le_of_le_le'

configureAnonymousSplitLemmas LogicIntros AbsIntros
