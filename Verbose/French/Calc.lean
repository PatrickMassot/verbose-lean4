import Verbose.Tactics.Calc
import Verbose.French.Common

namespace Lean.Elab.Tactic
open Meta Verbose French

declare_syntax_cat CalcFirstStepFR
syntax ppIndent(colGe term (" par " maybeAppliedFR)?) : CalcFirstStepFR
syntax ppIndent(colGe term (" puisque " factsFR)?) : CalcFirstStepFR
syntax ppIndent(colGe term (" car " tacticSeq)?) : CalcFirstStepFR

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStepFR
syntax ppIndent(colGe term " par " maybeAppliedFR) : CalcStepFR
syntax ppIndent(colGe term " puisque " factsFR) : CalcStepFR
syntax ppIndent(colGe term " car " tacticSeq) : CalcStepFR
syntax CalcStepFRs := ppLine withPosition(CalcFirstStepFR) withPosition((ppLine linebreak CalcStepFR)*)

syntax (name := calcTacticFR) "Calc" CalcStepFRs : tactic

elab tk:"sinceCalcTacFR" facts:factsFR : tactic => withRef tk <| sinceCalcTac (factsFRToArray facts)

def convertFirstCalcStepFR (step : TSyntax `CalcFirstStepFR) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStepFR|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStepFR|$t:term par $prf:maybeAppliedFR) => do let prfT ← maybeAppliedFRToTerm prf; `(calcFirstStep|$t := by fromCalcTac $prfT)
  | `(CalcFirstStepFR|$t:term puisque%$tk $facts:factsFR) => `(calcFirstStep|$t := by sinceCalcTacFR%$tk $facts)
  | `(CalcFirstStepFR|$t:term car $prf:tacticSeq) => `(calcFirstStep|$t := by $prf)
  | _ => throwUnsupportedSyntax


def convertCalcStepFR (step : TSyntax `CalcStepFR) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStepFR|$t:term par $prf:maybeAppliedFR) => do let prfT ← maybeAppliedFRToTerm prf; `(calcStep|$t := by fromCalcTac $prfT)
  | `(CalcStepFR|$t:term puisque%$tk $facts:factsFR) => `(calcStep|$t := by sinceCalcTacFR%$tk $facts)
  | `(CalcStepFR|$t:term car $prf:tacticSeq) => `(calcStep|$t := by $prf)
  | _ => throwUnsupportedSyntax

def convertCalcStepsFR (steps : TSyntax ``CalcStepFRs) : TermElabM (TSyntax ``calcSteps) := do
  match steps with
  | `(CalcStepFRs| $first:CalcFirstStepFR
       $steps:CalcStepFR*) => do
         let first ← convertFirstCalcStepFR first
         let steps ← steps.mapM convertCalcStepFR
         `(calcSteps|$first
           $steps*)
  | _ => throwUnsupportedSyntax


elab_rules : tactic
| `(tactic|Calc%$calcstx $stx) => do
  let steps : TSyntax ``CalcStepFRs := ⟨stx⟩
  let steps ← convertCalcStepsFR steps
  let some calcRange := (← getFileMap).rangeOfStx? calcstx | unreachable!
  let indent := calcRange.start.character
  let mut isFirst := true
  for step in ← Lean.Elab.Term.getCalcSteps steps do
    let some replaceRange := (← getFileMap).rangeOfStx? step | unreachable!
    let `(calcStep| $(_) := $proofTerm) := step | unreachable!
    let json := json% {"replaceRange": $(replaceRange),
                       "isFirst": $(isFirst),
                       "indent": $(indent)}
    Lean.Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) proofTerm
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))

implement_endpoint (lang := en) failProvingFacts (goal : Format) : CoreM String :=
pure s!"N’a pas pu prouver cela en utilisant les faits invoqués.\n{goal}"

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b car ring
  _ = 2*a*b + (a^2 + b^2) par add_comm
