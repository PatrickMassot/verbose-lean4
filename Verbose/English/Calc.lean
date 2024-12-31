import Verbose.Tactics.Calc
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
  for step in ← Lean.Elab.Term.mkCalcStepViews  steps do
    let some replaceRange := (← getFileMap).rangeOfStx? step.ref | unreachable!
    let json := json% {"replaceRange": $(replaceRange),
                       "isFirst": $(isFirst),
                       "indent": $(indent)}
    Lean.Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) step.proof
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))

implement_endpoint (lang := en) failProvingFacts (goal : Format) : CoreM String :=
pure s!"Failed to prove this using the provided facts.\n{goal}"

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b by ring
  _ = 2*a*b + (a^2 + b^2) from add_comm
