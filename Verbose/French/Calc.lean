import Verbose.Tactics.Calc
import Verbose.French.Common
import Verbose.French.We

section widget

open ProofWidgets
open Lean Meta

/-- Return the link text and inserted text above and below of the calc widget. -/
def verboseSuggestStepsFR (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams) :
    MetaM (String × String × Option (String.Pos × String.Pos)) := do
  let subexprPos := getGoalLocations pos
  let some (rel, lhs, rhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"
  let relApp := mkApp2 rel
    (← mkFreshExprMVar none)
    (← mkFreshExprMVar none)
  let some relStr := (← Meta.ppExpr relApp) |> toString |>.splitOn |>.get? 1
    | throwError "could not find relation symbol in {relApp}"
  let isSelectedLeft := subexprPos.any (fun L ↦ #[0, 1].isPrefixOf L.toArray)
  let isSelectedRight := subexprPos.any (fun L ↦ #[1].isPrefixOf L.toArray)

  let mut goalType := goalType
  for pos in subexprPos do
    goalType ← insertMetaVar goalType pos
  let some (_, newLhs, newRhs) ← Lean.Elab.Term.getCalcRelation? goalType | unreachable!

  let lhsStr := (toString <| ← Meta.ppExpr lhs).renameMetaVar
  let newLhsStr := (toString <| ← Meta.ppExpr newLhs).renameMetaVar
  let rhsStr := (toString <| ← Meta.ppExpr rhs).renameMetaVar
  let newRhsStr := (toString <| ← Meta.ppExpr newRhs).renameMetaVar

  let spc := String.replicate params.indent ' '
  let insertedCode := match isSelectedLeft, isSelectedRight with
  | true, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} car sorry\n{spc}_ {relStr} {newRhsStr} car sorry\n\
         {spc}_ {relStr} {rhsStr} car sorry"
    else
      s!"_ {relStr} {newLhsStr} car sorry\n{spc}\
         _ {relStr} {newRhsStr} car sorry\n{spc}\
         _ {relStr} {rhsStr} car sorry"
  | false, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newRhsStr} car sorry\n{spc}_ {relStr} {rhsStr} car sorry"
    else
      s!"_ {relStr} {newRhsStr} car sorry\n{spc}_ {relStr} {rhsStr} car sorry"
  | true, false =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} car sorry\n{spc}_ {relStr} {rhsStr} car sorry"
    else
      s!"_ {relStr} {newLhsStr} car sorry\n{spc}_ {relStr} {rhsStr} car sorry"
  | false, false => "This should not happen"

  let stepInfo := match isSelectedLeft, isSelectedRight with
  | true, true => "Create two new steps"
  | true, false | false, true => "Create a new step"
  | false, false => "This should not happen"
  let pos : String.Pos := insertedCode.find (fun c => c == '?')
  return (stepInfo, insertedCode, some (pos, ⟨pos.byteIdx + 2⟩) )

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
def VerboseCalcPanelFR.rpc := mkSelectionPanelRPC verboseSuggestStepsFR
  "Veuillez sélectionner une sous-expression dans le but."
  "Calc 🔍"

/-- The calc widget. -/
@[widget_module]
def WidgetCalcPanelFR : Component CalcParams :=
  mk_rpc_widget% VerboseCalcPanelFR.rpc
end widget

namespace Lean.Elab.Tactic
open Meta Verbose French

declare_syntax_cat CalcFirstStepFR
syntax ppIndent(colGe term (" par " sepBy(maybeAppliedFR, " et par "))?) : CalcFirstStepFR
syntax ppIndent(colGe term (" par calcul")?) : CalcFirstStepFR
syntax ppIndent(colGe term (" puisque " factsFR)?) : CalcFirstStepFR
syntax ppIndent(colGe term (" car " tacticSeq)?) : CalcFirstStepFR
syntax ppIndent(colGe term (" par?")?) : CalcFirstStepFR

-- Note: need to repeat "par" in first form since "et" can appear in maybeAppliedFR
declare_syntax_cat CalcStepFR
syntax ppIndent(colGe term " par " sepBy(maybeAppliedFR, " et par ")) : CalcStepFR
syntax ppIndent(colGe term " par calcul") : CalcStepFR
syntax ppIndent(colGe term " puisque " factsFR) : CalcStepFR
syntax ppIndent(colGe term " car " tacticSeq) : CalcStepFR
syntax ppIndent(colGe term " par?") : CalcStepFR

syntax CalcStepFRs := ppLine withPosition(CalcFirstStepFR) withPosition((ppLine linebreak CalcStepFR)*)

syntax (name := calcTacticFR) "Calc" CalcStepFRs : tactic

elab tk:"sinceCalcTacFR" facts:factsFR : tactic => withRef tk <| sinceCalcTac (factsFRToArray facts)

def convertFirstCalcStepFR (step : TSyntax `CalcFirstStepFR) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStepFR|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStepFR|$t:term par%$btk calcul%$ctk) =>
    run t btk ctk `(tacticSeq| On calcule)
  | `(CalcFirstStepFR|$t:term par%$tk $prfs et par*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedFRToTerm
    run t tk none `(tacticSeq| fromCalcTac $prfTs,*)
  | `(CalcFirstStepFR|$t:term puisque%$tk $facts:factsFR) =>
    run t tk none `(tacticSeq|sinceCalcTacFR%$tk $facts)
  | `(CalcFirstStepFR|$t:term car%$tk $prf:tacticSeq) =>
    run t tk none `(tacticSeq|$prf)
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

def convertCalcStepFR (step : TSyntax `CalcStepFR) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStepFR|$t:term par%$btk calcul%$ctk) =>
    run t btk ctk `(tacticSeq| On calcule)
  | `(CalcStepFR|$t:term par%$tk $prfs et par*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedFRToTerm
    run t tk none `(tacticSeq| fromCalcTac $prfTs,*)
  | `(CalcStepFR|$t:term puisque%$tk $facts:factsFR) =>
    run t tk none `(tacticSeq|sinceCalcTacFR%$tk $facts)
  | `(CalcStepFR|$t:term car%$tk $prf:tacticSeq) =>
    run t tk none `(tacticSeq|$prf)
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
  let indent := calcRange.start.character + 2
  let mut isFirst := true
  for step in ← Lean.Elab.Term.mkCalcStepViews  steps do
    let some replaceRange := (← getFileMap).rangeOfStx? step.ref | unreachable!
    let json := json% {"replaceRange": $(replaceRange),
                       "isFirst": $(isFirst),
                       "indent": $(indent)}
    Lean.Widget.savePanelWidgetInfo WidgetCalcPanelFR.javascriptHash (pure json) step.proof
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b par calcul
  _ = 2*a*b + (a^2 + b^2) par calcul

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + c    ≤ b + c par h
  _              ≤ b + d par h'

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
