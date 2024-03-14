-- Replace the next two imports by import Verbose.Tactics.Calc once it exists
import Verbose.Tactics.Since
import Verbose.Tactics.We
import Verbose.English.Common


namespace Lean.Elab.Tactic
open Meta Verbose English

declare_syntax_cat CalcFirstStep
syntax ppIndent(colGe term (" from " maybeApplied)?) : CalcFirstStep
syntax ppIndent(colGe term (" since " facts)?) : CalcFirstStep
syntax ppIndent(colGe term (" by " tacticSeq)?) : CalcFirstStep

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStep
syntax ppIndent(colGe term " from " maybeApplied) : CalcStep
syntax ppIndent(colGe term " since " facts) : CalcStep
syntax ppIndent(colGe term " by " tacticSeq) : CalcStep
syntax CalcSteps := ppLine withPosition(CalcFirstStep) withPosition((ppLine linebreak CalcStep)*)

syntax (name := calcTactic) "Calc" CalcSteps : tactic

section -- **MoveMe** to Verbose/Tactics/Calc.lean

open Linarith in
def tryLinarithOnly (goal : MVarId) (facts : List Term) : TacticM Bool := do
  let state ← saveState
  goal.withContext do
  let factsE ← facts.mapM (elabTerm · none)
  try
    linarith true factsE {preprocessors := defaultPreprocessors} goal
    return true
  catch _ =>
    restoreState state
    return false

def sinceConcludeCalcTac (facts : Array Term) : TacticM Unit := do
  let (newGoal, newFVarsT, _newFVars) ← sinceTac facts
  newGoal.withContext do
  let factsT : List Term := newFVarsT.toList ++ [(← `(And.intro)), (← `(And.left)), (← `(And.right))]
  if ← trySolveByElim newGoal factsT then
    return
  else if ← tryLinarithOnly newGoal newFVarsT.toList then
    return
  else
    throwError "Failed to prove this using the provided facts.\n{← Meta.ppGoal newGoal}"

def sinceRelCalcTac (facts : Array Term) : TacticM Unit := do
  -- logInfo s!"Running sinceRelCalcTact with {← liftM <| facts.mapM PrettyPrinter.ppTerm}"
  let (newGoal, newFVarsT, _newFVars) ← sinceTac facts
  newGoal.withContext do
  -- logInfo s!"Context after running sinceTac is\n {← Meta.ppGoal newGoal}"
  -- logInfo s!"fvars passed to gcongrForward are\n {← liftM <| newFVars.mapM FVarId.getUserName}"
  replaceMainGoal [newGoal]
  evalTactic (← `(tactic|rel [$newFVarsT,*]))
  /- let assum (_ : MVarId) := newGoal.gcongrForward (newFVars.map .fvar)
  let (_, _, unsolvedGoalStates) ← newGoal.gcongr none [] (mainGoalDischarger := assum)
  match unsolvedGoalStates.toList with
  -- if all goals are solved, succeed!
  | [] => pure ()
  -- if not, fail and report the unsolved goals
  | unsolvedGoalStates => do
    let unsolvedGoals ← @List.mapM MetaM _ _ _ MVarId.getType unsolvedGoalStates
    let g := Lean.MessageData.joinSep (unsolvedGoals.map Lean.MessageData.ofExpr) Format.line
    throwError "rel failed, cannot prove goal by 'substituting' the listed relationships. \
      The steps which could not be automatically justified were:\n{g}" -/

def sinceCalcTac (facts : Array Term) : TacticM Unit := do
  sinceConcludeCalcTac facts <|> sinceRelCalcTac facts

def fromRelCalcTac (prf : Term) : TacticM Unit := do
  -- logInfo s!"Running fromRelCalcTact with {prf}"
  evalTactic (← `(tactic| rel [$prf]))
  /- let goal ← getMainGoal
  goal.withContext do
  let hyp ← elabTerm prf none
  let assum (_ : MVarId) := goal.gcongrForward #[hyp]
  let (_, _, unsolvedGoalStates) ← goal.gcongr none [] (mainGoalDischarger := assum)
  match unsolvedGoalStates.toList with
  -- if all goals are solved, succeed!
  | [] => pure ()
  -- if not, fail and report the unsolved goals
  | unsolvedGoalStates => do
    let unsolvedGoals ← @List.mapM MetaM _ _ _ MVarId.getType unsolvedGoalStates
    let g := Lean.MessageData.joinSep (unsolvedGoals.map Lean.MessageData.ofExpr) Format.line
    throwError "rel failed, cannot prove goal by 'substituting' the listed relationships. \
      The steps which could not be automatically justified were:\n{g}"
 -/
def fromCalcTac (prf : Term) : TacticM Unit := do
  concludeTac prf <|> fromRelCalcTac prf

elab "fromCalcTac" prf:term : tactic => fromCalcTac prf

end -- of MoveMe

elab tk:"sinceCalcTac" facts:facts : tactic => withRef tk <| sinceCalcTac (factsToArray facts)

def convertFirstCalcStep (step : TSyntax `CalcFirstStep) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStep|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStep|$t:term from $prf:maybeApplied) => do let prfT ← maybeAppliedToTerm prf; `(calcFirstStep|$t := by fromCalcTac $prfT)
  | `(CalcFirstStep|$t:term since%$tk $facts:facts) => `(calcFirstStep|$t := by sinceCalcTac%$tk $facts)
  | `(CalcFirstStep|$t:term by $prf:tacticSeq) => `(calcFirstStep|$t := by $prf)
  | _ => throwUnsupportedSyntax


def convertCalcStep (step : TSyntax `CalcStep) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStep|$t:term from $prf:maybeApplied) => do let prfT ← maybeAppliedToTerm prf; `(calcStep|$t := by fromCalcTac $prfT)
  | `(CalcStep|$t:term since%$tk $facts:facts) => `(calcStep|$t := by sinceCalcTac%$tk $facts)
  | `(CalcStep|$t:term by $prf:tacticSeq) => `(calcStep|$t := by $prf)
  | _ => throwUnsupportedSyntax

def convertCalcSteps (steps : TSyntax ``CalcSteps) : TermElabM (TSyntax ``calcSteps) := do
  match steps with
  | `(CalcSteps| $first:CalcFirstStep
       $steps:CalcStep*) => do
         let first ← convertFirstCalcStep first
         let steps ← steps.mapM convertCalcStep
         `(calcSteps|$first
           $steps*)
  | _ => throwUnsupportedSyntax


elab_rules : tactic
| `(tactic|Calc%$calcstx $stx) => do
  let steps : TSyntax ``CalcSteps := ⟨stx⟩
  let steps ← convertCalcSteps steps
  let some calcRange := (← getFileMap).rangeOfStx? calcstx | unreachable!
  let indent := calcRange.start.character
  let mut isFirst := true
  for step in ← Lean.Elab.Term.getCalcSteps steps do
    let some replaceRange := (← getFileMap).rangeOfStx? step | unreachable!
    let `(calcStep| $(_) := $proofTerm) := step | unreachable!
    let json := open scoped Json in json% {"replaceRange": $(replaceRange),
                                                        "isFirst": $(isFirst),
                                                        "indent": $(indent)}
    Lean.Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) proofTerm
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))


example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b by ring
  _ = 2*a*b + (a^2 + b^2) from add_comm _ _
