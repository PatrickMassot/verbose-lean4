import Verbose.English.Common
namespace Lean.Elab.Tactic
open Meta

declare_syntax_cat CalcFirstStepFR
syntax ppIndent(colGe term (" par " term)?) : CalcFirstStepFR
syntax ppIndent(colGe term (" car " tacticSeq)?) : CalcFirstStepFR

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStepFR
syntax ppIndent(colGe term " par " term) : CalcStepFR
syntax ppIndent(colGe term " car " tacticSeq) : CalcStepFR
syntax CalcStepFRs := ppLine withPosition(CalcFirstStepFR) withPosition((ppLine linebreak CalcStepFR)*)

syntax (name := calcTacticFR) "Calc" CalcStepFRs : tactic

def convertFirstCalcStepFR (step : TSyntax `CalcFirstStepFR) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStepFR|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStepFR|$t:term par $prf:term) => `(calcFirstStep|$t := $prf)
  | `(CalcFirstStepFR|$t:term car $prf:tacticSeq) => `(calcFirstStep|$t := by $prf)
  | _ => throwUnsupportedSyntax


def convertCalcStepFR (step : TSyntax `CalcStepFR) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStepFR|$t:term par $prf:term) => `(calcStep|$t := $prf)
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
    let json := open scoped Json in json% {"replaceRange": $(replaceRange),
                                                        "isFirst": $(isFirst),
                                                        "indent": $(indent)}
    Lean.Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) proofTerm
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))


example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b car ring
  _ = 2*a*b + (a^2 + b^2) par add_comm _ _
