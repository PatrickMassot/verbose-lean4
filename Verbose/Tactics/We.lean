import Verbose.Tactics.Common

open Lean Parser Elab Tactic Linarith

/- Restore rewrite using a single term without brackets. -/
declare_syntax_cat myRwRuleSeq
syntax rwRule : myRwRuleSeq
syntax "[" rwRule,*,? "]" : myRwRuleSeq

def rewrite_macro (rw : Syntax) (s : TSyntax `myRwRuleSeq)
    (l : Option (TSyntax `Lean.Parser.Tactic.location)) : MacroM (TSyntax `tactic) :=
  match s with
  | `(myRwRuleSeq| [%$lbrak $rs:rwRule,* ]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (rewrite%$rw [%$lbrak $rs,*] $(l)?; try (with_reducible rfl%$rbrak)))
  | `(myRwRuleSeq| $rs:rwRule) =>
    `(tactic| (rewrite%$rw  [$rs] $(l)?; try (with_reducible rfl)))
  | _ => Macro.throwUnsupported

def discussOr (input : Term) : TacticM Unit := do
  evalApplyLikeTactic MVarId.apply <| ← `(Or.elim $input)

def discussEm (input : Term) : TacticM Unit := do
  evalApplyLikeTactic MVarId.apply <| ← `(Or.elim <| Classical.em $input)

def concludeTac (input : Term) : TacticM Unit := do
  evalExact (← `(tactic| exact $input ..)) <|> do
    let goal ← getMainGoal
    goal.withContext do
    let prf ← elabTerm input none
    linarith true [prf] {preprocessors := defaultPreprocessors} goal

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
  evalTactic (← `(tactic|iterate 3 (try first | done | fail_if_no_pro na_ring | fail_if_no_pro na_abel | fail_if_no_pro norm_num)))

def computeAtHypTac (loc : TSyntax `Lean.Parser.Tactic.location) : TacticM Unit := do
  evalTactic (← `(tactic| ((try first | fail_if_no_pro ring_nf $loc:location | fail_if_no_pro abel_nf $loc:location | skip); try (norm_num $loc:location); try (dsimp only $loc:location))))

def computeTac (loc? : Option (TSyntax `Lean.Parser.Tactic.location)) : TacticM Unit := do
  match loc? with
  | some loc => computeAtHypTac loc
  | none => computeAtGoalTac
