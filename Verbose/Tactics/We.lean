import Verbose.Tactics.Common

open Lean Meta Parser Elab Tactic Linarith

/- Restore rewrite using a single term without brackets. -/
syntax myRwRuleSeq := ("[" rwRule,*,? "]") <|> rwRule

instance : ToString Location := ⟨fun
| .wildcard => "*"
| .targets hyps type => toString hyps ++ if type then " ⊢" else ""⟩

def unexpandLocation : Location → MetaM (TSyntax `Lean.Parser.Tactic.location)
| .wildcard => `(Lean.Parser.Tactic.location| at *)
| .targets arr true => `(Lean.Parser.Tactic.location| at $(arr.map .mk):term* ⊢)
| .targets arr false => `(Lean.Parser.Tactic.location| at $(arr.map .mk):term*)

register_endpoint rwResultWithoutGoal : CoreM String

register_endpoint rwResultSeveralLoc : CoreM String

def rewriteTac (rw : Syntax) (s : TSyntax `myRwRuleSeq)
    (loc : Option Location) (new : Option Term) : TacticM Unit :=
  withMainContext do
  let l ← loc.mapM (fun l => unexpandLocation l)
  let tac : TSyntax `tactic ← match s with
  | `(myRwRuleSeq| [%$lbrak $rs:rwRule,* ]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (rewrite%$rw [%$lbrak $rs,*] $(l)?; try (with_reducible rfl%$rbrak)))
  | `(myRwRuleSeq| $rs:rwRule) =>
    `(tactic| (rewrite%$rw  [$rs] $(l)?; try (with_reducible rfl)))
  | _ => throwError ""
  evalTactic tac
  if let some t := new then
    let goal ← getMainGoal <|> throwError ← rwResultWithoutGoal
    goal.withContext do
    let fvarId? ← (do
    if new.isSome then
      match loc with
      | some (.targets #[stx] false) => return some (← getFVarId stx)
      | some (.targets #[] true) => return none
      | _ => throwError ← rwResultSeveralLoc
    else
      return none : TacticM (Option FVarId))
    match fvarId? with
    | some fvarId =>
        let newExpr ← fvarId.getType
        let actualNew ← elabTermEnsuringValue t (← instantiateMVars newExpr)
        replaceMainGoal [← goal.changeLocalDecl fvarId actualNew]
    | none =>
        let tgt ← instantiateMVars (← goal.getType)
        let actualNew ← elabTermEnsuringValue t tgt
        replaceMainGoal [← goal.change actualNew]

def discussOr (input : Term) : TacticM Unit := do
  evalApplyLikeTactic MVarId.apply <| ← `(Or.elim $input)

def discussEm (input : Term) : TacticM Unit := do
  evalApplyLikeTactic MVarId.apply <| ← `(Or.elim <| Classical.em $input)

variable (f : Nat → Nat → Nat)

register_endpoint cannotConclude : CoreM String

def concludeTac (input : Term) : TacticM Unit := withMainContext do
  (do { evalExact (← `(tactic| exact $input)) } <|>
   do { evalTactic (← `(tactic| focus apply $input;done)) } <|>
   do { let rule ← `(rwRule|$input:term)
        evalTactic (← `(tactic| focus rw [$rule]; first|done|rfl)) } <|>
   do {
     let goal ← getMainGoal
     goal.withContext do
     let prf ← elabTerm input none
     linarith true [prf] {preprocessors := defaultPreprocessors, splitNe := true} goal
  }) <|> do
  let _ ← elabTerm input none
  throwError (← cannotConclude)

def combineTac (prfs : Array Term) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let prfsExpr ← prfs.mapM (elabTerm · none)
  linarith true prfsExpr.toList {preprocessors := defaultPreprocessors, splitNe := true} goal


namespace Mathlib.Tactic
/- NOTE: This section is workaround until this fix is incorporated in Mathlib in #8482. -/

open Lean Meta Elab Tactic
/-- `fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the main goal
or the local context at reducible transparency. -/
syntax (name := failIfNoPro) "fail_if_no_pro " tacticSeq : tactic

/-- Run `tacs : TacticM Unit` on `goal`, and fail if no progress is made. -/
def runAndFailIfNoProgress' (goal : MVarId) (tacs : TacticM Unit) : TacticM (List MVarId) :=
  goal.withContext do
  let l ← run goal tacs
  try
    let [newGoal] := l | failure
    guard <|← withNewMCtxDepth <| withReducible <| isDefEq (← newGoal.getType) (← goal.getType)
    let ctxDecls := (← goal.getDecl).lctx.decls.toList
    let newCtxDecls := (← newGoal.getDecl).lctx.decls.toList
    guard <|← withNewMCtxDepth <| withReducible <| lctxIsDefEq ctxDecls newCtxDecls
  catch _ =>
    return l
  throwError "no progress made on {goal}"

elab_rules : tactic
| `(tactic| fail_if_no_pro $tacs) => do
  let goal ← getMainGoal
  let l ← runAndFailIfNoProgress' goal (evalTactic tacs)
  replaceMainGoal l
end Mathlib.Tactic

/-- The non-annoying abel tactic which does not pester users with `"Try this: abel_nf"`. -/
macro (name := abel) "na_abel" : tactic =>
  `(tactic| first | abel1 | abel_nf)

/-- The non-annoying ring tactic which does not pester users with `"Try this: ring_nf"`. -/
macro (name := ring) "na_ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

/-- Try to close the goal with simp only with the given lemmas. -/
def callSimp (lemmas : Array Name) : TacticM Bool := do
  let state ← saveState
  let simpThms ← simpTheoremsOfNames lemmas.toList (simpOnly := true)
  let cfg : Simp.Config := {}
  let ctx ← Simp.mkContext cfg (simpTheorems := #[simpThms])
    (congrTheorems := ← getSimpCongrTheorems)
  let goal ← getMainGoal
  let (newGoal?, _) ← simpTarget goal ctx
  if newGoal? matches none then
    return true
  else
    restoreState state
    return false

/-- Try to close the goal with simp only with lemmas in the compute lemma
configuration. -/
def tryComputeLemmas : TacticM Bool := withMainContext do
  let lemmas := (← verboseConfigurationExt.get).anonymousComputeLemmas
  trace[Verbose] s!"Will now try simplifying using anonymous compute lemmas: {lemmas}.
Goal is\n{← ppGoal (← getMainGoal)}"

  if ← callSimp lemmas then
    trace[Verbose] s!"Simplification sucessful!"
    return true
  else
    trace[Verbose] s!"Simplification failed."
    return true

elab "simp_compute" : tactic => unless ← tryComputeLemmas do failure

def gcongrDischarger (goal : MVarId) : MetaM Unit := Elab.Term.TermElabM.run' do
  trace[Meta.gcongr] "Attempting to discharge side goal {goal}"
  let [] ← Elab.Tactic.run goal <|
      Elab.Tactic.evalTactic (Unhygienic.run `(tactic| norm_num))
    | failure

def tryGcongrComputeLemmas : TacticM Bool := withMainContext do
  let state ← saveState
  let g ← getMainGoal
  let lemmas := (← verboseConfigurationExt.get).anonymousComputeLemmas
  trace[Verbose] s!"Will now try simplifying using gcongr and anonymous compute lemmas: {lemmas}.
Goal is\n{← ppGoal g}"
  let goals ← try
    let (_, _, unsolvedGoalStates) ← g.gcongr (sideGoalDischarger := gcongrDischarger) (mainGoalDischarger := fun g ↦ g.gcongrForward #[]) none []
    if unsolvedGoalStates == #[g] then
      trace[Verbose] s!"gcongr failed. Will try lemmas directly."
      restoreState state
    else
      trace[Verbose] s!"gcongr did something. {unsolvedGoalStates.size} goals remaining. main goal assigned: {← g.isAssigned}"
    pure unsolvedGoalStates
  catch
  | _ =>
    trace[Verbose] s!"gcongr failed."
    restoreState state
    pure #[]
  for goal in goals do
    trace[Verbose] "gcongr_compute working on goal\n{← ppGoal goal}"
    for lem in lemmas do
      trace[Verbose] "Try to apply lemma {lem}"
      if let some newGoals ← tryLemma goal lem then
        trace[Verbose] "lemma applied"
        if newGoals matches [] then
          trace[Verbose] "goal closed"
          break
    if ← notM goal.isAssigned then
      trace[Verbose] "goal not closed, giving up"
      restoreState state
      return false
  return true

elab "gcongr_compute" : tactic => unless ← tryGcongrComputeLemmas do failure

register_endpoint computeFailed (goal : MessageData) : TacticM MessageData

elab "check_suitable" : tactic => withMainContext do
  let t ← getMainTarget
  if t.isForall || t.isAppOf `Iff || t.isAppOf `And || t.isAppOf `Or then
    failure

def computeAtGoalTac : TacticM Unit := do
  try
    evalTactic (← `(tactic|focus (check_suitable; (iterate 3 (try first | done | rfl | fail_if_no_pro simp_compute | fail_if_no_pro gcongr_compute | fail_if_no_pro na_ring | fail_if_no_pro norm_num | fail_if_no_pro na_abel)); done)))
  catch
  | _ => throwError (← computeFailed (← getMainTarget))

def computeAtHypTac (loc : TSyntax `Lean.Parser.Tactic.location) : TacticM Unit := do
  evalTactic (← `(tactic| ((try first | fail_if_no_pro ring_nf $loc:location | norm_num $loc:location | skip); try (fail_if_no_pro abel_nf $loc:location); try (dsimp only $loc:location))))

def computeTac (loc? : Option (TSyntax `Lean.Parser.Tactic.location)) : TacticM Unit := do
  match loc? with
  | some loc => computeAtHypTac loc
  | none => computeAtGoalTac


section fixed_push_neg
/- In this section we fix an oversight in the `push_neg.use_distrib` option.
Because bounded existential quantifiers are defined using `And` in Lean 4,
this option does the wrong thing to negate them. We fix this by using ad hoc simp
lemmas after using `push_neg`. -/

lemma push_neg_fix₁ {α : Type*} [LinearOrder α] (P : α → Prop) (a : α) :
    (∀ x, a < x ∨ P x) ↔ ∀ x ≤ a, P x := by
  simp_rw [← not_le (b := a), imp_iff_not_or]

lemma push_neg_fix₂ {α : Type*} [LinearOrder α] (P : Prop) (a : α) :
    (∀ x, a ≤ x ∨ P) ↔ ∀ x < a, P := by
  simp_rw [← not_lt (b := a), imp_iff_not_or]

lemma push_neg_fix₃ {α : Type*} [LinearOrder α] (P : α → Prop) (a : α) :
(∀ x : α, x < a ∨ P x) ↔ ∀ (x : α), x ≥ a → P x := by
  simp_rw [← not_lt (b := a), imp_iff_not_or, not_not]

lemma push_neg_fix₄ {α : Type*} [LinearOrder α] (P : α → Prop) (a : α) :
    (∀ x : α, x ≤ a ∨ P x) ↔ ∀ (x : α), x > a → P x := by
  simp_rw [← not_le (b := a), imp_iff_not_or, not_not]

lemma push_neg_fix₅ {α : Type*} (s : Set α) (P : α → Prop) :
    (∀ x : α, x ∉ s ∨ P x) ↔ ∀ (x : α), x ∈ s → P x := by
  simp_rw [imp_iff_not_or]

lemma push_neg_fix₆ {α : Type*} (s : Set α) (P : α → Prop) :
    (∀ x : α, x ∈ s ∨ P x) ↔ ∀ (x : α), x ∉ s → P x := by
  simp_rw [imp_iff_not_or, not_not]

open Mathlib.Tactic.PushNeg in
elab "fixed_push_neg" loc:(location)? : tactic => do
  evalTactic (←
    `(tactic|(
       set_option push_neg.use_distrib true in
       push_neg $[$loc]?
       try
         simp only [push_neg_fix₁, push_neg_fix₂, push_neg_fix₃, push_neg_fix₄, push_neg_fix₅, push_neg_fix₆] $[$loc]?)))

set_option linter.unusedVariables false in
example (h : ¬ (∃ x > 4, 0 < x)) : True := by
  fixed_push_neg at h
  guard_hyp h : ∀ x > 4, x ≤ 0
  trivial

set_option linter.unusedVariables false in
example (h : ¬ (∃ x ∈ (Set.univ : Set ℕ), 0 < x)) : True := by
  fixed_push_neg at h
  guard_hyp h : ∀ x ∈ (Set.univ : Set ℕ), x ≤ 0
  trivial

example : ¬ (∃ x > 4, 0 < x) ↔ ∀ x > 4, x ≤ 0 := by
  fixed_push_neg

end fixed_push_neg

register_endpoint cannotContrapose : CoreM String

def contraposeTac (pushNeg : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← whnf (← getMainTarget)
  unless tgt.isForall do
    throwError ← cannotContrapose
  let p := tgt.bindingDomain!
  let q := tgt.bindingBody!
  unless (← inferType p).isProp && (← inferType q).isProp do
    throwError ← cannotContrapose
  let newGoals ← goal.apply (.const ``Mathlib.Tactic.Contrapose.mtr [])
  replaceMainGoal newGoals
  if pushNeg then
    evalTactic (← `(tactic| try fixed_push_neg))

def pushNegTac (loc? : Option Location) (new? : Option Term) : TacticM Unit := withMainContext do
  let l ← loc?.mapM (fun l => unexpandLocation l)
  evalTactic (← `(tactic|fixed_push_neg $[$l]?))
  if (← getGoals) matches [] then
    return
  let goal ← getMainGoal
  goal.withContext do
  if let some newT := new? then
    match loc? with
    | some loc =>
      match loc with
      | .targets #[stx] false =>
        let fvarId ← getFVarId stx
        let newE ← elabTermEnsuringValue newT (← instantiateMVars (← fvarId.getType))
        replaceMainGoal [← goal.changeLocalDecl fvarId newE]
      | _ => pure ()
    | none =>
      let newE ← elabTermEnsuringValue newT (← getMainTarget)
      let newGoal ← goal.change newE
      replaceMainGoal [newGoal]

-- The next two tactics are workarounds until https://github.com/leanprover/lean4/pull/6483 lands

elab "guard_hyp_strict" hyp:ident " : " val:term : tactic => withMainContext do
    let fvarid ← getFVarId hyp
    let lDecl ←
      match (← getLCtx).find? fvarid with
      | none => throwError m!"hypothesis {hyp} not found"
      | some lDecl => pure lDecl
    let e ← elabTerm val none
    let hty ← instantiateMVars lDecl.type
    unless e.equal hty do
      throwError m!"hypothesis {hyp} has type{indentExpr hty}\nnot{indentExpr e}"

set_option linter.unusedVariables false in
example (h : ∃ k : Nat, k = k) : True := by
  success_if_fail_with_msg "hypothesis h has type
  ∃ k, k = k
not
  ∃ l, l = l
"
    guard_hyp_strict h : ∃ l : Nat, l = l -- I hoped this would have failed
  trivial

elab "guard_target_strict" val:term : tactic => withMainContext do
    let tgt ← getMainTarget
    let e ← elabTerm val none
    unless e.equal tgt do
      throwError "target of main goal is{indentExpr tgt}\nnot{indentExpr e}"

example : ∃ k : Nat, k = k := by
  success_if_fail_with_msg "target of main goal is
  ∃ k, k = k
not
  ∃ l, l = l
"
    guard_target_strict ∃ l : Nat, l = l -- I hoped this would have failed
  use 0

register_endpoint unfoldResultSeveralLoc : CoreM String

def unfoldTac (tgt : Ident) (loc : Option (TSyntax `Lean.Parser.Tactic.location))
    (new? : Option Term) :  TacticM Unit := do
  evalTactic (← `(tactic| unfold $tgt $[$loc:location]?))
  if let some new := new? then
    match loc.map expandLocation with
      | some (.targets #[stx] false) => evalTactic (← `(tactic| guard_hyp_strict $(.mk stx):ident : $new))
      | some (.targets #[] true) | none => evalTactic (← `(tactic| guard_target_strict $new))
      | some _ => throwError ← unfoldResultSeveralLoc

section renameBVar_fix
namespace Verbose
-- This section backports the fix from https://github.com/leanprover-community/mathlib4/pull/20743
open Lean Expr Meta Parser Elab Tactic Mathlib Tactic
/-- Traverses an expression `e` and renames bound variables named `old` to `new`. -/
def renameBVar (e : Expr) (old new : Name) : Expr :=
  match e with
  | app fn arg => app (fn.renameBVar old new) (arg.renameBVar old new)
  | lam n ty bd bi =>
    lam (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | forallE n ty bd bi =>
    forallE (if n == old then new else n) (ty.renameBVar old new) (bd.renameBVar old new) bi
  | mdata d e' => mdata d (e'.renameBVar old new)
  | e => e

def renameBVarHyp (mvarId : MVarId) (fvarId : FVarId) (old new : Name) :
    MetaM Unit :=
  modifyLocalDecl mvarId fvarId fun ldecl ↦
    ldecl.setType <| ldecl.type.renameBVar old new
/-- Renames a bound variable in the target. -/
def renameBVarTarget (mvarId : MVarId) (old new : Name) : MetaM Unit :=
  modifyTarget mvarId fun e ↦ e.renameBVar old new
end Verbose
end renameBVar_fix
register_endpoint renameResultSeveralLoc : CoreM String

open Mathlib Tactic in
def renameTac (old new : Ident) (loc? : Option (TSyntax `Lean.Parser.Tactic.location))
    (becomes? : Option Term) := do
  let mvarId ← getMainGoal
  instantiateMVarDeclMVars mvarId
  match loc? with
  | none => Verbose.renameBVarTarget mvarId old.getId new.getId
  | some loc =>
    withLocation (expandLocation loc)
      (fun fvarId ↦ Verbose.renameBVarHyp mvarId fvarId old.getId new.getId)
      (Verbose.renameBVarTarget mvarId old.getId new.getId)
      fun _ ↦ throwError "unexpected location syntax"
  -- TODO: factor out the next six lines that are duplicated from unfoldTac
  if let some becomes := becomes? then
    match loc?.map expandLocation with
      | some (.targets #[stx] false) => evalTactic (← `(tactic| guard_hyp_strict $(.mk stx):ident : $becomes))
      | some (.targets #[] true) | none => evalTactic (← `(tactic| guard_target_strict $becomes))
      | some _ => throwError ← renameResultSeveralLoc
