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

def paire_fun  (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f g : ℝ → ℝ) : paire_fun f → paire_fun g →  paire_fun (f + g) := by
  intro hf hg
  show ∀ x, (f+g) (-x) = (f+g) x
  intro x₀
  Calc (f + g) (-x₀) = f (-x₀) + g (-x₀) par calcul
  _                  = f x₀ + g (-x₀)    puisque f (-x₀) = f x₀
  _                  = f x₀ + g x₀       puisque g (-x₀) = g x₀
  _                  = (f + g) x₀        par calcul

example (f g : ℝ → ℝ) : paire_fun f →  paire_fun (g ∘ f) := by
  intro hf x
  Calc (g ∘ f) (-x) = g (f (-x)) par calcul
                _   = g (f x)    puisque f (-x) = f x

example (f : ℝ → ℝ) (x : ℝ) (hx : f (-x) = f x ∧ 1 = 1) : f (-x) + 0 = f x := by
  Calc f (-x) + 0 = f (-x) par calcul
                _   = f x  puisque f (-x) = f x

example (f g : ℝ → ℝ) (hf : paire_fun f) (hg : paire_fun g) (x) :  (f+g) (-x) = (f+g) x := by
  Calc (f + g) (-x) = f (-x) + g (-x) par calcul
  _                 = f x + g (-x)    puisque paire_fun f
  _                 = f x + g x       puisque paire_fun g
  _                 = (f + g) x       par calcul
