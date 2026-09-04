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
register_endpoint inductionBaseError : CoreM String
register_endpoint inductionUnexpectedError : CoreM String
register_endpoint inductionBinderError : CoreM String

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
  let .forallE bn bt body .. := stmt_expr |
    throwError ← inductionError
  if not (← isDefEq bt (mkConst ``Nat)) then
    throwError ← inductionError

  -- Try to see whether the goal is a specialization of the announced statement.
  let argMVar ← mkFreshExprMVar (some <| .const `Nat [])
  let arg? ←
    if ← isDefEq (body.instantiate1 argMVar) (← orig_goal.getType >>= instantiateMVars) then
      getExprMVarAssignment? argMVar.mvarId!
    else
      pure none

  let (subGoal, mainGoal, _) ← claim' orig_goal hyp_name stmt_expr
  subGoal.withContext do
    let (n_fvar, newest_goal) ← subGoal.intro1P
    let goals ← newest_goal.induction n_fvar ``Nat.rec #[{varNames := []}, {varNames := [bn, `hyp_rec]}]
    let #[base_subgoal, ind_subgoal] := goals | throwError "Inductive proof failed"
    let (_, ind_case) ← ind_subgoal.mvarId.revert (goals[1]!.fields.map Expr.fvarId!)
    replaceMainGoal [base_subgoal.mvarId, ind_case, mainGoal]
    evalTactic (← `(tactic|
      (simp_rw [Nat.zero_eq]
       on_goal 2 => simp_rw [Nat.succ_eq_add_one])))
    if let some arg := arg? then
      trace[Verbose] "Goal is a special case of inductively proven fact"
      evalTactic (← `(tactic| on_goal 3 => exact $(mkIdent hyp_name) _))
      if let some argFVar := arg.fvarId? then
        trace[Verbose] "This special case is application to a free variable, will clear it."
        let argName ← argFVar.getUserName
        evalTactic (← `(tactic|
          (on_goal 1 => clear! $(mkIdent argName)
           on_goal 2 => clear! $(mkIdent argName))))
    else
      evalTactic (← `(tactic| on_goal 3 => try (exact $(mkIdent hyp_name))))

lemma Nat.le_induction_shift {k : ℕ} {P : ℕ → Prop} (h : ∀ n, P (n + k)) : ∀ n ≥ k, P n := by
  intro n hn
  simpa [hn] using h (n - k)

lemma Nat.le_base_split {k : ℕ} {P : ℕ → Prop} (top : P (k + 1)) (rest : ∀ n, n ≤ k → P n) :
    ∀ n, n ≤ k + 1 → P n := by
  intro n hn
  obtain h | h := le_iff_lt_or_eq.mp hn
  · exact rest n (Nat.lt_succ_iff.mp h)
  · exact h ▸ top

lemma Nat.lt_base_split {k : ℕ} {P : ℕ → Prop} (top : P k) (rest : ∀ n < k, P n) :
    ∀ n < k + 1, P n := by
  sorry

lemma Nat.le_base_zero {P : ℕ → Prop} : (∀ n, n ≤ 0 → P n) ↔ P 0 := by
  constructor
  · intro hn
    exact hn _ (by lia)
  · intro h0 n hn
    simp only [nonpos_iff_eq_zero] at hn
    exact hn ▸ h0

lemma Nat.lt_base_zero {P : ℕ → Prop} : (∀ n, n < 0 → P n) ↔ True := by
  simp
lemma Nat.lt_base_one {P : ℕ → Prop} : (∀ n, n < 1 → P n) ↔ P 0 := by
  simp


theorem rec_with_bases {motive : ℕ → Prop} {n₀ : ℕ}
    (base : ∀ n, n ≤ n₀ → motive n)
    (step : ∀ n ≥ n₀, motive n → motive (n + 1)) :
    ∀ n, motive n := by
  intro n
  induction n
  · exact base 0 (by lia)
  next n hn =>
    by_cases hk : n < n₀
    · apply base _ (by lia)
    · apply step _ (by lia) hn

lemma le_induction_shift_undo_weak {n₀ : ℕ} {P : ℕ → Prop} {k : ℕ} (h : ∀ n ≥ n₀ + k, P n → P (n + 1)) : ∀ n ≥ n₀, P (n + k) → P ((n + 1) + k) := by
  intro n hn hnk
  rw [show n + 1 + k = n + k + 1 by ring]
  exact h _ (by omega) hnk

lemma le_induction_shift_undo_strong {n₀ : ℕ} {P : ℕ → Prop} {shift : ℕ}
    (h : ∀ n ≥ (n₀ + shift), (∀ k < n, k ≥ shift → P k) → P n) :
  ∀ n ≥ n₀, (∀ k < n, P (k + shift)) → P (n + shift) := by
  intro n hn h'
  apply h _ (by lia)
  intro k hk hk'
  simpa [show k - shift + shift = k by lia] using h' (k - shift) (by lia)


lemma le_induction_shift_undo_strong_bases {n₀ : ℕ} {P : ℕ → Prop} {shift : ℕ} (h : ∀ n ≥ (n₀ + shift), (∀ k ≤ n, k ≥ shift → P k) → P (n + 1)) : ∀ n ≥ n₀, (∀ k ≤ n, P (k + shift)) → P ((n + 1) + shift) := by
  intro n hn h'
  rw [show n + 1 + shift = n + shift + 1 by ring]
  apply h _ (by lia)
  intro k hk hk'
  rw [show k = k - shift + shift by lia]
  apply h'
  lia

theorem strongRec {motive : ℕ → Prop} {n₀ : ℕ}
    (base : ∀ n < n₀, motive n)
    (step : ∀ n ≥ n₀, (∀ k , k < n → motive k) → motive n) :
    ∀ n, motive n := by
  intro n
  induction n using Nat.strongRec
  next n hn =>
    by_cases hn₀ : n < n₀
    · exact base _ hn₀
    · exact step _ (by lia) hn

-- Strictly speaking, the base cases could be n < n₀. However, students find strong induction
-- without base cases very confusing, and this formulation always retains a base case.
theorem strongRec_with_bases {motive : ℕ → Prop} {n₀ : ℕ}
    (base : ∀ n, n ≤ n₀ → motive n)
    (step : ∀ n ≥ n₀, (∀ k , k ≤ n → motive k) → motive (n + 1)) :
    ∀ n, motive n := by
  intro n
  induction n using Nat.strong_induction_on
  next k hm =>
    match k with
    | 0 => exact base _ (by lia)
    | k + 1 =>
      by_cases hk : k < n₀
      · exact base _ (by lia)
      · apply step _ (by lia)
        intro k' hk'
        exact hm _ (by lia)

theorem geq_zero_imp {p : Prop} {n : ℕ} : (n ≥ 0 → p) ↔ p := by simp

/--
  This function provides a flexible induction setup:
  - Supports strong and weak induction
  - Supports multiple base cases (only contiguous integers)
-/
def letsInductFlex (binderName : Name) (weak : Bool := true) (rawBases : Array Syntax := #[]) : TacticM Unit := do
  trace[Verbose] "Entering letsInductFlex"
  let orig_goal ← getMainGoal
  orig_goal.withContext do
  let goalTypeRaw ← orig_goal.getType >>= instantiateMVars
  let goalType ← whnf goalTypeRaw
  let .forallE bn bt body .. := goalType  |
    trace[Verbose] "Goal does not start with forall quantifier"
    throwError ← inductionError
  trace[Verbose] "Extracted body {body}"

  if bn != binderName then
    trace[Verbose] "Wrong binder name"
    throwError ← inductionBinderError
  if not (← isDefEq bt (mkConst ``Nat)) then
    trace[Verbose] "Wrong binder type"
    throwError ← inductionError

  -- If the goal starts an implication with a lower bound on the variable,
  -- capture that bound, else the lower bound is zero
  -- motiveBody contains an expr with the natural at de Bruijn index 0
  let ⟨lowerboundOpt, isStrict, dependentOnBound, motiveBody⟩ : Option Nat × Bool × Bool × Expr :=
    match body with
    | .forallE _ ineqType innerBody _ =>
      if innerBody.hasLooseBVar 0 then
        ⟨.none, false, true, body⟩
      else
        match ineqType.getAppFnArgs with
        -- Only support lower bounds with literal numbers
        | (``LE.le, #[_, _, n, .bvar _]) => ⟨n.nat?, false, false, innerBody.lowerLooseBVars 1 1⟩
        | (``GE.ge, #[_, _, .bvar _, n]) => ⟨n.nat?, false, false, innerBody.lowerLooseBVars 1 1⟩
        | (``LT.lt, #[_, _, n, .bvar _]) => ⟨n.nat?, true, false, innerBody.lowerLooseBVars 1 1⟩
        | (``GT.gt, #[_, _, .bvar _, n]) => ⟨n.nat?, true, false, innerBody.lowerLooseBVars 1 1⟩
        | _ => ⟨.none, false, false, body⟩
      | _ => ⟨.some 0, false, false, body⟩

  if dependentOnBound then
    trace[Verbose] "Motive depends on bound"
    throwError ← inductionUnexpectedError

  let origMotive := Expr.lam bn bt motiveBody .default
  if lowerboundOpt.isNone then
    trace[Verbose] "No lower bound detected"
    throwError ← inductionUnexpectedError
  let lowerbound := if isStrict then lowerboundOpt.get! + 1 else lowerboundOpt.get!

  let bases ← rawBases.mapM fun s => do
    match s.isNatLit? with
    | some n => pure n
    | none => throwError ← inductionBaseError

  -- Validation of base cases
  let baseCases := if bases.isEmpty then #[0] else bases.map (· - lowerbound)
  trace[Verbose] "baseCases: {baseCases}"

  unless baseCases.qsort (· < ·) == Array.range baseCases.size do
    trace[Verbose] "Wrong base cases";
    throwError ← inductionBaseError

  let numBaseSplits := baseCases.size - 1

  -- Shift the index to only have two recursors that both start at 0
  let motiveShifted ←
    if lowerbound = 0 then
      pure origMotive
    else
      withLocalDeclD `m (mkConst ``Nat) fun m => do
        let shift ← (mkAdd m (mkNatLit lowerbound))
        mkLambdaFVars #[m] (mkApp origMotive shift).headBeta

  trace[Verbose] "Working with motive: {motiveShifted}"

  let strongRecBases := (← verboseConfigurationExt.get).useBaseCasesForStrongInduction

  -- Choose recursor based on strong or weak induction
  let recursor :=
    if weak then
      ``rec_with_bases
    else
      if strongRecBases then
        ``strongRec_with_bases
      else
        ``strongRec

  trace[Verbose] "Modifying goals"
  if lowerbound != 0 then
    evalTactic (← `(tactic| refine Nat.le_induction_shift (k := $(Syntax.mkNatLit lowerbound)) ?_))

  let curGoal ← getMainGoal
  trace[Verbose] "Applying recursor"
  let recExpr ← mkConstWithFreshMVarLevels recursor
  let goals ← curGoal.apply <| mkApp recExpr motiveShifted
  trace[Verbose] "Applied recursor"

  let n₀ := if !weak ∧ !strongRecBases ∧ !rawBases.isEmpty then numBaseSplits + 1 else numBaseSplits

  let ⟨baseGoal, indGoal⟩ ←
    let #[base, ind, n0] := goals.toArray |
      -- Should really be unreachable
      trace[Verbose] "Unexpected number of goals from applying recursor"
      throwError ← inductionUnexpectedError
    n0.assign (mkNatLit n₀)
    pure (base, ind)

  -- Limited simp setup
  let simprocs_add ← ({} : Simprocs).add ``Nat.reduceAdd false
  let simprocs ← simprocs_add.add ``Nat.reduceSub false
  let ctx ← Simp.mkContext {} (simpTheorems := #[])

  -- Split base goals into multiple cases
  let mut baseGoals : Array MVarId := #[]
  let mut remaining := baseGoal
  for _ in [0:numBaseSplits] do
    trace[Verbose] "Splitting base cases"
    let splitLemma := if weak ∨ strongRecBases then
        ``Nat.le_base_split
      else
        ``Nat.lt_base_split

    let split ← remaining.apply (← mkConstWithFreshMVarLevels splitLemma)
    let #[top, rest] := split.toArray |
      -- Should really be unreachable
      trace[Verbose] "Not exactly two goals when stating base cases"
      throwError ← inductionUnexpectedError
    let ⟨simpedTop, _⟩ ← simpTarget top ctx #[simprocs]

    baseGoals := baseGoals.push <| simpedTop.getD top
    remaining := rest

  trace[Verbose] "Treating goals for the zero case"
  let zeroSimpTheorems ← simpTheoremsOfNames [``Nat.le_base_zero, ``Nat.lt_base_zero, ``Nat.lt_base_one] (simpOnly := true)
  let zeroCtx ← Simp.mkContext {} (simpTheorems := #[zeroSimpTheorems])
  let ⟨simpedZeroGoal, _⟩ ← simpTarget remaining zeroCtx #[simprocs]

  -- This simplifies both ∀ n ≥ 0, and n ≥ 0 → ...
  let simpTheorems ← simpTheoremsOfNames [``geq_zero_imp] (simpOnly := true)
  let forallSimpCtx ← Simp.mkContext {} (simpTheorems := #[simpTheorems])
  let unshiftLemma :=
    if weak then
      ``le_induction_shift_undo_weak
    else
      if strongRecBases then
        ``le_induction_shift_undo_strong_bases
      else
        ``le_induction_shift_undo_strong
  let unshiftExpr ← mkConstWithFreshMVarLevels unshiftLemma

  trace[Verbose] "Unshifting induction"
  let shiftedIndGoals ← indGoal.apply <| (mkAppN unshiftExpr #[mkNatLit n₀, origMotive, mkNatLit lowerbound]).headBeta
  let simpedIndGoals ← shiftedIndGoals.mapM (fun goal => do
    let ⟨newGoal, _⟩ ←  simpTarget goal forallSimpCtx #[simprocs]
    pure <| newGoal.getD goal)

  setGoals ([simpedZeroGoal.getD remaining] ++ baseGoals.toList.reverse ++ simpedIndGoals)

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
