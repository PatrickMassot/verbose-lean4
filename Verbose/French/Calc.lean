import Verbose.Tactics.Calc
import Verbose.French.Common
import Verbose.French.We

namespace Lean.Elab.Tactic
open Meta Verbose French

declare_syntax_cat CalcFirstStepFR
syntax ppIndent(colGe term (" par " sepBy(maybeAppliedFR, " et par "))?) : CalcFirstStepFR
syntax ppIndent(colGe term (" par calcul")?) : CalcFirstStepFR
syntax ppIndent(colGe term (" puisque " factsFR)?) : CalcFirstStepFR
syntax ppIndent(colGe term (" car " tacticSeq)?) : CalcFirstStepFR

-- Note: need to repeat "par" in first form since "et" can appear in maybeAppliedFR
declare_syntax_cat CalcStepFR
syntax ppIndent(colGe term " par " sepBy(maybeAppliedFR, " et par ")) : CalcStepFR
syntax ppIndent(colGe term " par calcul") : CalcStepFR
syntax ppIndent(colGe term " puisque " factsFR) : CalcStepFR
syntax ppIndent(colGe term " car " tacticSeq) : CalcStepFR
syntax CalcStepFRs := ppLine withPosition(CalcFirstStepFR) withPosition((ppLine linebreak CalcStepFR)*)

syntax (name := calcTacticFR) "Calc" CalcStepFRs : tactic

elab tk:"sinceCalcTacFR" facts:factsFR : tactic => withRef tk <| sinceCalcTac (factsFRToArray facts)

def convertFirstCalcStepFR (step : TSyntax `CalcFirstStepFR) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStepFR|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStepFR|$t:term par calcul) => `(calcFirstStep|$t:term := by On calcule)
  | `(CalcFirstStepFR|$t:term par $prfs et par*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedFRToTerm
    `(calcFirstStep|$t := by fromCalcTac $prfTs,*)
  | `(CalcFirstStepFR|$t:term puisque%$tk $facts:factsFR) => `(calcFirstStep|$t := by sinceCalcTacFR%$tk $facts)
  | `(CalcFirstStepFR|$t:term car $prf:tacticSeq) => `(calcFirstStep|$t := by $prf)
  | _ => throwUnsupportedSyntax


def convertCalcStepFR (step : TSyntax `CalcStepFR) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStepFR|$t:term par $prfs et par*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedFRToTerm
    `(calcStep|$t := by fromCalcTac $prfTs,*)
  | `(CalcStepFR|$t:term par calcul) => `(calcStep|$t:term := by On calcule)
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
  for step in ← Lean.Elab.Term.mkCalcStepViews steps do
    let some replaceRange := (← getFileMap).rangeOfStx? step.ref | unreachable!
    let json := json% {"replaceRange": $(replaceRange),
                       "isFirst": $(isFirst),
                       "indent": $(indent)}
    Lean.Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) step.proof
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))

implement_endpoint (lang := fr) failProvingFacts (goal : Format) : CoreM String :=
pure s!"La preuve de cela en utilisant les faits invoqués a échoué.\n{goal}"

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b par calcul
  _ = 2*a*b + (a^2 + b^2) par calcul

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c par calcul
  _              ≤ b + c par h
  _              ≤ b + d par h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c par calcul
  _              ≤ b + c puisque a ≤ b
  _              ≤ b + d puisque c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c par calcul
  _              ≤ b + d puisque a ≤ b et c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c par calcul
  _              ≤ b + d par h et par h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c par calcul
  _              ≤ b + d par h et par h'
