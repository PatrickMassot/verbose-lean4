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

def computeAtGoalTac : TacticM Unit := do
  evalTactic (← `(tactic|iterate 3 (first | done | ring_nf | abel | norm_num)))

def computeAtHypTac (loc : TSyntax `Lean.Parser.Tactic.location) : TacticM Unit := do
  evalTactic (← `(tactic| ((first | ring_nf $loc:location | abel $loc:location | skip); try (norm_num $loc:location); try (dsimp only $loc:location))))

def computeTac (loc? : Option (TSyntax `Lean.Parser.Tactic.location)) : TacticM Unit := do
  match loc? with
  | some loc => computeAtHypTac loc
  | none => computeAtGoalTac
