import Verbose.Tactics.Calc
import Verbose.English.Common
import Verbose.English.We
import Verbose.English.By

section widget

open ProofWidgets
open Lean Meta

implement_endpoint (lang := en) getSince? : MetaM String := pure "since?"
implement_endpoint (lang := en) createOneStepMsg : MetaM String := pure "Create a new step"
implement_endpoint (lang := en) createTwoStepsMsg : MetaM String := pure "Create two new steps"

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
def VerboseCalcPanel.rpc := mkSelectionPanelRPC' verboseSuggestSteps
  "Please select some subexpressions in the goal using shift-click."
  "New calculation step creation"
  (extraCss := some "#suggestions {display:none}")

/-- The calc widget. -/
@[widget_module]
def WidgetCalcPanel : Component CalcParams :=
  mk_rpc_widget% VerboseCalcPanel.rpc

implement_endpoint (lang := en) mkComputeCalcTac : MetaM String := pure "by computation"
implement_endpoint (lang := en) mkComputeCalcDescr : MetaM String := pure "Justify by computation"
implement_endpoint (lang := en) mkComputeAssptTac : MetaM String := pure "by hypothesis"
implement_endpoint (lang := en) mkComputeAssptDescr : MetaM String := pure "Justify by assumption"
implement_endpoint (lang := en) mkSinceCalcTac : MetaM String := pure "since"
implement_endpoint (lang := en) mkSinceCalcHeader : MetaM String := pure "Justify using"
implement_endpoint (lang := en) mkSinceCalcArgs (args : Array Format) : MetaM String := do
  return match args with
  | #[] => ""
  | #[x] => s!"{x}"
  | a => ", ".intercalate ((a[:a.size-1]).toArray.toList.map (toString)) ++ s!" and {a[a.size-1]!}"

configureCalcSuggestionProvider verboseSelectSince

implement_endpoint (lang := en) theSelectedSubExpr : MetaM String :=
  pure "The selected sub-expression"
implement_endpoint (lang := en) allSelectedSubExpr : MetaM String :=
  pure "All selected sub-expressions"
implement_endpoint (lang := en) inMainGoal : MetaM String :=
  pure "in the main goal."
implement_endpoint (lang := en) inMainGoalOrCtx : MetaM String :=
  pure "in the main goal or its context."
implement_endpoint (lang := en) shouldBe : MetaM String :=
  pure "should be"
implement_endpoint (lang := en) shouldBePl : MetaM String :=
  pure "should be"
implement_endpoint (lang := en) selectOnlyOne : MetaM String :=
  pure "You should select only one sub-expression."

/-- Rpc function for the calc justification widget. -/
@[server_rpc_method]
def VerboseCalcSincePanel.rpc := mkSelectionPanelRPC' (onlyGoal := false) getCalcSuggestion
  "You can select some local assumption."
  "Justification"
  verboseGetDefaultCalcSuggestions
  (extraCss := some "#suggestions {display:none}")

/-- The calc justification widget. -/
@[widget_module]
def WidgetCalcSincePanel : Component CalcParams :=
  mk_rpc_widget% VerboseCalcSincePanel.rpc
end widget

namespace Lean.Elab.Tactic
open Meta Verbose English

declare_syntax_cat CalcFirstStep
syntax ppIndent(colGe term (" from "  sepBy(maybeApplied, " and from "))?) : CalcFirstStep
syntax ppIndent(colGe term (" by hypothesis")?) : CalcFirstStep
syntax ppIndent(colGe term (" by computation")?) : CalcFirstStep
syntax ppIndent(colGe term (" since " facts)?) : CalcFirstStep
syntax ppIndent(colGe term (" since?")?) : CalcFirstStep
syntax ppIndent(colGe term (" by " tacticSeq)?) : CalcFirstStep

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStep
syntax ppIndent(colGe term " from " sepBy(maybeApplied, " and from ")) : CalcStep
syntax ppIndent(colGe term " by hypothesis") : CalcStep
syntax ppIndent(colGe term " by computation") : CalcStep
syntax ppIndent(colGe term " since " facts) : CalcStep
syntax ppIndent(colGe term " since?") : CalcStep
syntax ppIndent(colGe term " by " tacticSeq) : CalcStep
syntax CalcSteps := ppLine withPosition(CalcFirstStep) withPosition((ppLine linebreak CalcStep)*)

syntax (name := calcTactic) "Calc" CalcSteps : tactic

elab tk:"sinceCalcTac" facts:facts : tactic => withRef tk <| sinceCalcTac (factsToArray facts)

def convertFirstCalcStep (step : TSyntax `CalcFirstStep) : TermElabM (TSyntax ``calcFirstStep × Option Syntax) := do
  match step with
  | `(CalcFirstStep|$t:term) => pure (← `(calcFirstStep|$t:term), none)
  | `(CalcFirstStep|$t:term by%$btk hypothesis%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| strg_assumption), none)
  | `(CalcFirstStep|$t:term by%$btk computation%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| We compute), none)
  | `(CalcFirstStep|$t:term from%$tk $prfs and from*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcFirstStep|$t:term since%$tk $facts:facts) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTac%$tk $facts), none)
  | `(CalcFirstStep|$t:term since?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcFirstStep|$t:term by%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|$prf), none)
  | _ => throwUnsupportedSyntax
where
  run (t : Term) (btk : Syntax) (ctk? : Option Syntax)
      (tac : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
      TermElabM (TSyntax `Lean.calcFirstStep) := do
    let ctk := ctk?.getD btk
    let tacs ← withRef ctk tac
    let pf ← withRef step.raw[1] `(term| by%$btk $tacs)
    let pf := pf.mkInfoCanonical
    withRef step <| `(calcFirstStep|$t:term := $pf)

def convertCalcStep (step : TSyntax `CalcStep) : TermElabM (TSyntax ``calcStep × Option Syntax) := do
  match step with
  | `(CalcStep|$t:term by%$btk hypothesis%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| strg_assumption), none)
  | `(CalcStep|$t:term by%$btk computation%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| We compute), none)
  | `(CalcStep|$t:term from%$tk $prfs and from*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcStep|$t:term since%$tk $facts:facts) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTac%$tk $facts), none)
  | `(CalcStep|$t:term since?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcStep|$t:term by%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|$prf), none)
  | _ => throwUnsupportedSyntax
where
  run (t : Term) (btk : Syntax) (ctk? : Option Syntax)
      (tac : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
      TermElabM (TSyntax `Lean.calcStep) := do
    let ctk := ctk?.getD btk
    let tacs ← withRef ctk tac
    let pf ← withRef step.raw[1] `(term| by%$btk $tacs)
    let pf := pf.mkInfoCanonical
    withRef step <| `(calcStep|$t:term := $pf)

def convertCalcSteps (steps : TSyntax ``CalcSteps) : TermElabM (TSyntax ``calcSteps × Array (Option Syntax)) := do
  match steps with
  | `(CalcSteps| $first:CalcFirstStep
       $steps:CalcStep*) => do
         let (first, tk?) ← convertFirstCalcStep first
         let mut newsteps := #[]
         let mut tks? := #[tk?]
         for step in steps do
           let (newstep, tk?) ← convertCalcStep step
           newsteps := newsteps.push newstep
           tks? := tks?.push tk?
         pure (← `(calcSteps|$first
           $newsteps*), tks?)
  | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic|Calc%$calcstx $stx) => do
  let steps : TSyntax ``CalcSteps := ⟨stx⟩
  let (steps, tks?) ← convertCalcSteps steps
  let views ← Lean.Elab.Term.mkCalcStepViews steps
  if (← verboseConfigurationExt.get).useCalcWidget then
    if let some calcRange := (← getFileMap).rangeOfStx? calcstx then
    let indent := calcRange.start.character + 2
    let mut isFirst := true
    for (step, tk?) in views.zip tks? do
      if let some replaceRange := (← getFileMap).rangeOfStx? step.ref then
        let json := json% {"replaceRange": $(replaceRange),
                           "isFirst": $(isFirst),
                           "indent": $(indent)}
        Lean.Widget.savePanelWidgetInfo WidgetCalcPanel.javascriptHash (pure json) step.proof
      if let some tk := tk? then
        if let some replaceRange := (← getFileMap).rangeOfStx? tk then
          let json := json% {"replaceRange": $(replaceRange),
                             "isFirst": $(isFirst),
                             "indent": $(indent)}
          Lean.Widget.savePanelWidgetInfo WidgetCalcSincePanel.javascriptHash (pure json) tk
      isFirst := false
  evalVerboseCalc (← `(tactic|calc%$calcstx $steps))

syntax (name := Calc?) "Calc?" : tactic

elab "Calc?" : tactic =>
  mkCalc?Tac "Create a computation" "Calc" "since?"

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b   by computation
    _           = 2*a*b + (a^2 + b^2) by computation

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + c    ≤ b + c from h
  _              ≤ b + d from h'

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

example (ε : ℝ) (h : ε > 1) : 0 ≤ ε := by
  Calc
    (0 : ℝ) ≤ 1 by norm_num
    _       < ε from h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Calc
    (0 : ℝ) ≤ 1 by norm_num
    _       < ε from h

example (ε : ℝ) (h : ε = 1) : ε+1 ≥ 2 := by
  Calc
    ε + 1 = 1 + 1 by rw [h]
    _     = 2 by norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≤ 2 := by
  Calc
    ε + 1 = 1 + 1 by rw [h]
    _     = 2 by norm_num

example (f : ℝ → ℝ) (h : ∀ x, f (f x) = x) : f (f 0) + 0 = 0 := by
  Calc f (f 0) + 0 = f (f 0) by computation
       _           = 0       by hypothesis

example (f : ℝ → ℝ) (h : ∀ x, f (f x) = x) : f (f 0) = 0 + 0 := by
  Calc f (f 0) = 0      by hypothesis
       _       = 0  + 0 by computation
