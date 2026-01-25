import Verbose.Tactics.Calc
import Verbose.French.Common
import Verbose.French.We

section widget

open ProofWidgets
open Lean Meta

implement_endpoint (lang := fr) getSince? : MetaM String := pure "par?"
implement_endpoint (lang := fr) createOneStepMsg : MetaM String := pure "Créer une nouvelle étape"
implement_endpoint (lang := fr) createTwoStepsMsg : MetaM String := pure "Créer deux nouvelles étapes"

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
def VerboseCalcPanelFR.rpc := mkSelectionPanelRPC' verboseSuggestSteps
  "Veuillez sélectionner une sous-expression du but."
  "Création de nouvelle étape de calcul"
  (extraCss := some "#suggestions {display:none}")

/-- The calc widget. -/
@[widget_module]
def WidgetCalcPanelFR : Component CalcParams :=
  mk_rpc_widget% VerboseCalcPanelFR.rpc

implement_endpoint (lang := fr) mkComputeCalcTac : MetaM String := pure "par calcul"
implement_endpoint (lang := fr) mkComputeCalcDescr : MetaM String := pure "Justifier par calcul"
implement_endpoint (lang := fr) mkComputeAssptTac : MetaM String := pure "par hypothèse"
implement_endpoint (lang := fr) mkComputeAssptDescr : MetaM String := pure "Justifier par hypothèse"
implement_endpoint (lang := fr) mkSinceCalcTac : MetaM String := pure "puisque"
implement_endpoint (lang := fr) mkSinceCalcHeader : MetaM String := pure "Justifier par"
implement_endpoint (lang := fr) mkSinceCalcArgs (args : Array Format) : MetaM String := do
  return match args with
  | #[] => ""
  | #[x] => s!"{x}"
  | a => ", ".intercalate ((a[:a.size-1]).toArray.toList.map (toString)) ++ s!" et {a[a.size-1]!}"

configureCalcSuggestionProvider verboseSelectSince

implement_endpoint (lang := fr) theSelectedSubExpr : MetaM String :=
  pure "L’expression sélectionnée"
implement_endpoint (lang := fr) allSelectedSubExpr : MetaM String :=
  pure "Toutes les expressions sélectionnée"
implement_endpoint (lang := fr) inMainGoal : MetaM String :=
  pure "dans le but principal."
implement_endpoint (lang := fr) inMainGoalOrCtx : MetaM String :=
  pure "dans le but principal ou son contexte."
implement_endpoint (lang := fr) shouldBe : MetaM String :=
  pure "doit être"
implement_endpoint (lang := fr) shouldBePl : MetaM String :=
  pure "doivent être"
implement_endpoint (lang := fr) selectOnlyOne : MetaM String :=
  pure "Vous devez sélectionner au moins une expression."
implement_endpoint (lang := fr) factCannotJustifyStep : CoreM String :=
  return  "Ce fait ne permet pas de justifier directement cette étape."
implement_endpoint (lang := fr) factsCannotJustifyStep : CoreM String :=
  return "Les faits listés ne permettent pas de justifier directement cette étape."

/-- Rpc function for the calc justification widget. -/
@[server_rpc_method]
def VerboseCalcSincePanelFR.rpc := mkSelectionPanelRPC' (onlyGoal := false) getCalcSuggestion
  "Vous pouvez sélectionner une ou plusieurs hypothèses à utiliser."
  "Justification"
  verboseGetDefaultCalcSuggestions
  (extraCss := some "#suggestions {display:none}")

/-- The calc justification widget. -/
@[widget_module]
def WidgetCalcSincePanelFR : Component CalcParams :=
  mk_rpc_widget% VerboseCalcSincePanelFR.rpc
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

def convertFirstCalcStepFR (step : TSyntax `CalcFirstStepFR) : TermElabM (TSyntax ``calcFirstStep × Option Syntax) := do
  match step with
  | `(CalcFirstStepFR|$t:term) => pure (← `(calcFirstStep|$t:term), none)
  | `(CalcFirstStepFR|$t:term par%$btk calcul%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| On calcule), none)
  | `(CalcFirstStepFR|$t:term par%$tk $prfs et par*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedFRToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcFirstStepFR|$t:term puisque%$tk $facts:factsFR) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTacFR%$tk $facts), none)
  | `(CalcFirstStepFR|$t:term par?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcFirstStepFR|$t:term car%$tk $prf:tacticSeq) =>
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

def convertCalcStepFR (step : TSyntax `CalcStepFR) : TermElabM (TSyntax ``calcStep × Option Syntax) := do
  match step with
  | `(CalcStepFR|$t:term par%$btk calcul%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| On calcule), none)
  | `(CalcStepFR|$t:term par%$tk $prfs et par*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedFRToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcStepFR|$t:term puisque%$tk $facts:factsFR) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTacFR%$tk $facts), none)
  | `(CalcStepFR|$t:term par?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcStepFR|$t:term car%$tk $prf:tacticSeq) =>
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

def convertCalcStepsFR (steps : TSyntax ``CalcStepFRs) : TermElabM (TSyntax ``calcSteps × Array (Option Syntax)) := do
  match steps with
  | `(CalcStepFRs| $first:CalcFirstStepFR
       $steps:CalcStepFR*) => do
         let (first, tk?) ← convertFirstCalcStepFR first
         let mut newsteps := #[]
         let mut tks? := #[tk?]
         for step in steps do
           let (newstep, tk?) ← convertCalcStepFR step
           newsteps := newsteps.push newstep
           tks? := tks?.push tk?
         pure (← `(calcSteps|$first
           $newsteps*), tks?)
  | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic|Calc%$calcstx $stx) => do
  let steps : TSyntax ``CalcStepFRs := ⟨stx⟩
  let (steps, tks?) ← convertCalcStepsFR steps
  let views ← Lean.Elab.Term.mkCalcStepViews steps
  if (← verboseConfigurationExt.get).useCalcWidget then
    if let some calcRange := (← getFileMap).lspRangeOfStx? calcstx then
    let indent := calcRange.start.character + 2
    let mut isFirst := true
    for (step, tk?) in views.zip tks? do
      if let some replaceRange := (← getFileMap).lspRangeOfStx? step.ref then
        let json := json% {"replaceRange": $(replaceRange),
                           "isFirst": $(isFirst),
                           "indent": $(indent)}
        Lean.Widget.savePanelWidgetInfo WidgetCalcPanelFR.javascriptHash (pure json) step.proof
      if let some tk := tk? then
        if let some replaceRange := (← getFileMap).lspRangeOfStx? tk then
          let json := json% {"replaceRange": $(replaceRange),
                             "isFirst": $(isFirst),
                             "indent": $(indent)}
          Lean.Widget.savePanelWidgetInfo WidgetCalcSincePanelFR.javascriptHash (pure json) tk
      isFirst := false
  evalVerboseCalc (← `(tactic|calc%$calcstx $steps))

syntax (name := Calc?FR) "Calc?" : tactic

elab "Calc?" : tactic =>
  mkCalc?Tac "Création de calcul" "Calc" "par?"

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b par calcul
  _ = 2*a*b + (a^2 + b^2) par calcul

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + c    ≤ b + c par h
   _            ≤ b + d par h'

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


example (ε : ℝ) (h : ε > 1) : 0 ≤ ε := by
  Calc
    (0 : ℝ) ≤ 1 car norm_num
    _       < ε par h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Calc
    (0 : ℝ) ≤ 1 car norm_num
    _       < ε par h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Calc
    ε > 1 par h
    _ > 0 car norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≥ 2 := by
  Calc
    ε + 1 = 1 + 1 car rw [h]
    _     = 2 par norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≤ 2 := by
  Calc
    ε + 1 = 1 + 1 car rw [h]
    _     = 2 par norm_num

example (u : ℕ → ℝ) (y) (hy : ∀ n, u n = y) (n m) : u n = u m := by
  Calc
    u n = y puisque ∀ n, u n = y
    _   = u m puisque ∀ n, u n = y


-- Next four examples check casting capabilities

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N > 0 := by
  success_if_fail_with_msg "'calc' expression has type
  3 > 0
but is expected to have type
  N > 0"
    Calc
      3 ≥ 1/ε par?
      _ > 0 par ε_pos
  Calc
    N ≥ 1/ε par hN
    _ > 0 par ε_pos

-- Combine with relaxed calc now
example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N ≥ 0 := by
  success_if_fail_with_msg "'calc' expression has type
  3 > 0
but is expected to have type
  N ≥ 0"
    Calc
      3 ≥ 1/ε par?
      _ > 0 par ε_pos
  Calc
    N ≥ 1/ε par hN
    _ > 0 par ε_pos

-- A case where the conclusion has an extra cast
example (N : ℕ) (hN : N ≥ 3) : N > (1 : ℝ) := by
  Calc
    N ≥ 3 par hN
    _ > 1 par calcul

-- Combine with relaxed calc now
example (N : ℕ) (hN : N ≥ 3) : N ≥ (1 : ℝ) := by
  Calc
    N ≥ 3 par hN
    _ > 1 par calcul
