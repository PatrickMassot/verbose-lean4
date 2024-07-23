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
      | some (.targets #[stx] false) => some (← getFVarId stx)
      | some (.targets #[] true) => none
      | _ => throwError ← rwResultSeveralLoc
    else
      none : TacticM (Option FVarId))
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

-- FIXME: this function does not work as expected. Waiting for Zulip help
def addEllipsis (x : Term) : CoreM Term := `($x ..)

/- elab "do_nothing" x:term : command => do
  dbg_trace x

elab "add_ellipsis" x:term : command => do
  let y ← Command.liftCoreM <| addEllipsis x
  dbg_trace y

add_ellipsis f
do_nothing f ..
add_ellipsis f 1
do_nothing f 1 .. -/

def concludeTac (input : Term) : TacticM Unit := do
  do { evalExact (← `(tactic| exact $input)) } <|> do {
  let input' ← addEllipsis input
  evalExact (← `(tactic| exact $input')) } <|> do {
    let rule ← `(rwRule|$input:term)
    evalTactic (← `(tactic| rw [$rule]; first|done|rfl)) } <|>
  do {
    let goal ← getMainGoal
    goal.withContext do
    let prf ← elabTerm input none
    linarith true [prf] {preprocessors := defaultPreprocessors} goal
  }

def combineTac (prfs : Array Term) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let prfsExpr ← prfs.mapM (elabTerm · none)
  linarith true prfsExpr.toList {preprocessors := defaultPreprocessors} goal


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


def computeAtGoalTac : TacticM Unit := do
  evalTactic (← `(tactic|focus iterate 3 (try first | done | fail_if_no_pro na_ring | fail_if_no_pro norm_num | fail_if_no_pro na_abel)))

def computeAtHypTac (loc : TSyntax `Lean.Parser.Tactic.location) : TacticM Unit := do
  evalTactic (← `(tactic| ((try first | fail_if_no_pro ring_nf $loc:location | norm_num $loc:location | skip); try (fail_if_no_pro abel_nf $loc:location); try (dsimp only $loc:location))))

def computeTac (loc? : Option (TSyntax `Lean.Parser.Tactic.location)) : TacticM Unit := do
  match loc? with
  | some loc => computeAtHypTac loc
  | none => computeAtGoalTac

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
    evalTactic (← `(tactic| set_option push_neg.use_distrib true in try push_neg))

def pushNegTac (loc? : Option Location) (new? : Option Term) : TacticM Unit := do
  let l ← loc?.mapM (fun l => unexpandLocation l)
  evalTactic (← `(tactic|set_option push_neg.use_distrib true in push_neg $[$l]?))
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
