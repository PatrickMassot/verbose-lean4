import Verbose.English.Common
namespace Lean.Elab.Tactic
open Meta

declare_syntax_cat CalcFirstStep
syntax ppIndent(colGe term (" from " term)?) : CalcFirstStep
syntax ppIndent(colGe term (" by " tacticSeq)?) : CalcFirstStep

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStep
syntax ppIndent(colGe term " from " term) : CalcStep
syntax ppIndent(colGe term " by " tacticSeq) : CalcStep
syntax CalcSteps := ppLine withPosition(CalcFirstStep) withPosition((ppLine linebreak CalcStep)*)

syntax (name := calcTactic) "Calc" CalcSteps : tactic

def convertFirstCalcStep (step : TSyntax `CalcFirstStep) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStep|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStep|$t:term from $prf:term) => `(calcFirstStep|$t := $prf)
  | `(CalcFirstStep|$t:term by $prf:tacticSeq) => `(calcFirstStep|$t := by $prf)
  | _ => throwUnsupportedSyntax


def convertCalcStep (step : TSyntax `CalcStep) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStep|$t:term from $prf:term) => `(calcStep|$t := $prf)
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
    let json := open scoped Std.Json in json% {"replaceRange": $(replaceRange),
                                                        "isFirst": $(isFirst),
                                                        "indent": $(indent)}
    ProofWidgets.savePanelWidgetInfo proofTerm `CalcPanel (pure json)
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))


example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b by ring
  _ = 2*a*b + (a^2 + b^2) from add_comm _ _
