import Verbose.Tactics.Calc
import Verbose.English.Common
import Verbose.English.We

namespace Lean.Elab.Tactic
open Meta Verbose English

declare_syntax_cat CalcFirstStep
syntax ppIndent(colGe term (" from "  sepBy(maybeApplied, " and from "))?) : CalcFirstStep
syntax ppIndent(colGe term (" by computation")?) : CalcFirstStep
syntax ppIndent(colGe term (" since " facts)?) : CalcFirstStep
syntax ppIndent(colGe term (" by " tacticSeq)?) : CalcFirstStep

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStep
syntax ppIndent(colGe term " from " sepBy(maybeApplied, " and from ")) : CalcStep
syntax ppIndent(colGe term " by computation") : CalcStep
syntax ppIndent(colGe term " since " facts) : CalcStep
syntax ppIndent(colGe term " by " tacticSeq) : CalcStep
syntax CalcSteps := ppLine withPosition(CalcFirstStep) withPosition((ppLine linebreak CalcStep)*)

syntax (name := calcTactic) "Calc" CalcSteps : tactic

elab tk:"sinceCalcTac" facts:facts : tactic => withRef tk <| sinceCalcTac (factsToArray facts)

def convertFirstCalcStep (step : TSyntax `CalcFirstStep) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStep|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStep|$t:term by computation) => `(calcFirstStep|$t:term := by We compute)
  | `(CalcFirstStep|$t:term from $prfs and from*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedToTerm
    `(calcFirstStep|$t := by fromCalcTac $prfTs,*)
  | `(CalcFirstStep|$t:term since%$tk $facts:facts) => `(calcFirstStep|$t := by sinceCalcTac%$tk $facts)
  | `(CalcFirstStep|$t:term by $prf:tacticSeq) => `(calcFirstStep|$t := by $prf)
  | _ => throwUnsupportedSyntax


def convertCalcStep (step : TSyntax `CalcStep) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStep|$t:term from $prfs and from*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedToTerm
    `(calcStep|$t := by fromCalcTac $prfTs,*)
  | `(CalcStep|$t:term by computation) => `(calcStep|$t:term := by We compute)
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

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b   by computation
   _           = 2*a*b + (a^2 + b^2) by computation

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c by computation
  _              ≤ b + c from h
  _              ≤ b + d from h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c by computation
  _              ≤ b + c since a ≤ b
  _              ≤ b + d since c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c by computation
  _              ≤ b + d since a ≤ b and c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c by computation
  _              ≤ b + d from h and from h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c by computation
  _              ≤ b + d from h and from h'

def even_fun  (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f g : ℝ → ℝ) : even_fun f → even_fun g →  even_fun (f + g) := by
  intro hf hg
  show ∀ x, (f+g) (-x) = (f+g) x
  intro x₀
  Calc (f + g) (-x₀) = f (-x₀) + g (-x₀) by computation
  _                  = f x₀ + g (-x₀)    since f (-x₀) = f x₀
  _                  = f x₀ + g x₀       since g (-x₀) = g x₀
  _                  = (f + g) x₀        by computation

example (f g : ℝ → ℝ) : even_fun f →  even_fun (g ∘ f) := by
  intro hf x
  Calc (g ∘ f) (-x) = g (f (-x)) by computation
                _   = g (f x)    since f (-x) = f x

example (f : ℝ → ℝ) (x : ℝ) (hx : f (-x) = f x ∧ 1 = 1) : f (-x) + 0 = f x := by
  Calc f (-x) + 0 = f (-x) by computation
                _   = f x  since f (-x) = f x

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) (x) :  (f+g) (-x) = (f+g) x := by
  Calc (f + g) (-x) = f (-x) + g (-x) by computation
  _                 = f x + g (-x)    since even_fun f
  _                 = f x + g x       since even_fun g
  _                 = (f + g) x       by computation
