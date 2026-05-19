import Verbose.Tactics.Calc
import Verbose.Spanish.Common
import Verbose.Spanish.We
import Verbose.Spanish.By

section widget

open ProofWidgets
open Lean Meta

implement_endpoint (lang := es) getSince? : MetaM String := pure "usando?"
implement_endpoint (lang := es) createOneStepMsg : MetaM String := pure "Crea un nuevo paso"
implement_endpoint (lang := es) createTwoStepsMsg : MetaM String := pure "Crea dos nuevos pasos"

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
def VerboseCalcPanelES.rpc := mkSelectionPanelRPC' verboseSuggestSteps
  "Selecciona una sub-expresión de la meta haciendo shift-click."
  "Creación de un nuevo paso de calculo"
  (extraCss := some "#suggestions {display:none}")

/-- The calc widget. -/
@[widget_module]
def WidgetCalcPanelES : Component CalcParams :=
  mk_rpc_widget% VerboseCalcPanelES.rpc

implement_endpoint (lang := es) mkComputeCalcTac : MetaM String := pure "por cálculo"
implement_endpoint (lang := es) mkComputeCalcDescr : MetaM String := pure "Verificar por cálculo"
implement_endpoint (lang := es) mkComputeAssptTac : MetaM String := pure "por hipótesis"
implement_endpoint (lang := es) mkComputeAssptDescr : MetaM String := pure "Verificar por hipótesis"
implement_endpoint (lang := es) mkSinceCalcTac : MetaM String := pure "Como"
implement_endpoint (lang := es) mkSinceCalcHeader : MetaM String := pure "Verificar usando"
implement_endpoint (lang := es) mkSinceCalcArgs (args : Array Format) : MetaM String := do
  return match args with
  | #[] => ""
  | #[x] => s!"{x}"
  | a => ", ".intercalate ((a[:a.size-1]).toArray.toList.map (toString)) ++ s!" y {a[a.size-1]!}"

configureCalcSuggestionProvider verboseSelectSince

implement_endpoint (lang := es) theSelectedSubExpr : MetaM String :=
  pure "La expresión seleccionada"
implement_endpoint (lang := es) allSelectedSubExpr : MetaM String :=
  pure "Todas las expresiones seleccionadas"
implement_endpoint (lang := es) inMainGoal : MetaM String :=
  pure "en la meta principal."
implement_endpoint (lang := es) inMainGoalOrCtx : MetaM String :=
  pure "en la meta principal o dentro de su contexto."
implement_endpoint (lang := es) shouldBe : MetaM String :=
  pure "deberíá ser"
implement_endpoint (lang := es) shouldBePl : MetaM String :=
  pure "deberían"
implement_endpoint (lang := es) selectOnlyOne : MetaM String :=
  pure "Tienes que seleccionar al menos una sub-expresión."
implement_endpoint (lang := es) factCannotJustifyStep : CoreM String :=
  return  "Esta información no justifica directamente este paso."
implement_endpoint (lang := es) factsCannotJustifyStep : CoreM String :=
  return  "La información proporcionada no justifica directamente este paso."

/-- Rpc function for the calc justification widget. -/
@[server_rpc_method]
def VerboseCalcSincePanelES.rpc := mkSelectionPanelRPC' (onlyGoal := false) getCalcSuggestion
  "Puedes seleccionar una o más hipótesis para usar."
  "Justificación"
  verboseGetDefaultCalcSuggestions
  (extraCss := some "#suggestions {display:none}")

/-- The calc justification widget. -/
@[widget_module]
def WidgetCalcSincePanelES : Component CalcParams :=
  mk_rpc_widget% VerboseCalcSincePanelES.rpc
end widget

namespace Lean.Elab.Tactic
open Meta Verbose Spanish

declare_syntax_cat CalcFirstStepES
syntax ppIndent(colGe term (" por "  sepBy(maybeAppliedES, " yy "))?) : CalcFirstStepES
/- syntax ppIndent(colGe term (" por hipótesis")?) : CalcFirstStepES -/
syntax ppIndent(colGe term (" por cálculo")?) : CalcFirstStepES
syntax ppIndent(colGe term (" ya que " factsES)?) : CalcFirstStepES
syntax ppIndent(colGe term (" usando?")?) : CalcFirstStepES
syntax ppIndent(colGe term (" usando " tacticSeq)?) : CalcFirstStepES

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStepES
syntax ppIndent(colGe term " por " sepBy(maybeAppliedES, " yy ")) : CalcStepES
/- syntax ppIndent(colGe term " por hipótesis") : CalcStepES -/
syntax ppIndent(colGe term " por cálculo") : CalcStepES
syntax ppIndent(colGe term " ya que " factsES) : CalcStepES
syntax ppIndent(colGe term " usando?") : CalcStepES
syntax ppIndent(colGe term " usando " tacticSeq) : CalcStepES

syntax calcStepsES := ppLine withPosition(CalcFirstStepES) withPosition((ppLine linebreak CalcStepES)*)

syntax (name := calcTacticES) "Calc" calcStepsES : tactic

elab tk:"comoCalcTac" factsES:factsES : tactic => withRef tk <| sinceCalcTac (factsESToArray factsES)

def convertFirstCalcStepES (step : TSyntax `CalcFirstStepES) : TermElabM (TSyntax ``calcFirstStep × Option Syntax) := do
  match step with
  | `(CalcFirstStepES|$t:term) => pure (← `(calcFirstStep|$t:term), none)
/-   | `(CalcFirstStepES|$t:term por%$btk hipótesis%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| asunción), none) -/
  | `(CalcFirstStepES|$t:term por%$btk cálculo%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| computeCalcTac), none)
  | `(CalcFirstStepES|$t:term por%$tk $prfs yy*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedESToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcFirstStepES|$t:term ya que%$tk $factsES:factsES) =>
    pure (← run t tk none `(tacticSeq|comoCalcTac%$tk $factsES), none)
  | `(CalcFirstStepES|$t:term usando?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcFirstStepES|$t:term usando%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|tacSeqCalcTac $prf), none)
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

def convertCalcStepES (step : TSyntax `CalcStepES) : TermElabM (TSyntax ``calcStep × Option Syntax) := do
  match step with
/-   | `(CalcStepES|$t:term por%$btk hipótesis%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| asunción), none) -/
  | `(CalcStepES|$t:term por%$btk cálculo%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| computeCalcTac), none)
  | `(CalcStepES|$t:term por%$tk $prfs yy*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedESToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcStepES|$t:term ya que%$tk $factsES:factsES) =>
    pure (← run t tk none `(tacticSeq|comoCalcTac%$tk $factsES), none)
  | `(CalcStepES|$t:term usando?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcStepES|$t:term usando%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|tacSeqCalcTac $prf), none)
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

def convertCalcStepsES (steps : TSyntax ``calcStepsES) : TermElabM (TSyntax ``calcSteps × Array (Option Syntax)) := do
  match steps with
  | `(calcStepsES| $first:CalcFirstStepES
       $steps:CalcStepES*) => do
         let (first, tk?) ← convertFirstCalcStepES first
         let mut newsteps := #[]
         let mut tks? := #[tk?]
         for step in steps do
           let (newstep, tk?) ← convertCalcStepES step
           newsteps := newsteps.push newstep
           tks? := tks?.push tk?
         pure (← `(calcSteps|$first
           $newsteps*), tks?)
  | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic|Calc%$calcstx $stx) => do
  let steps : TSyntax ``calcStepsES := ⟨stx⟩
  let (steps, tks?) ← convertCalcStepsES steps
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
        Lean.Widget.savePanelWidgetInfo WidgetCalcPanelES.javascriptHash (pure json) step.proof
      if let some tk := tk? then
        if let some replaceRange := (← getFileMap).lspRangeOfStx? tk then
          let json := json% {"replaceRange": $(replaceRange),
                             "isFirst": $(isFirst),
                             "indent": $(indent)}
          Lean.Widget.savePanelWidgetInfo WidgetCalcSincePanelES.javascriptHash (pure json) tk
      isFirst := false
  evalVerboseCalc (← `(tactic|calc%$calcstx $steps))

syntax (name := Calc?ES) "Calc?" : tactic

elab "Calc?" : tactic =>
  mkCalc?Tac "Creación del cálculo" "Calc" "usando?"

setLang es

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  success_if_fail_with_msg "Unknown identifier `x`"
    Calc (x+b)^2 = a^2 + b^2 + 2*a*b por cálculo
    _ = 2*a*b + (a^2 + b^2) por cálculo
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b   por cálculo
    _           = 2*a*b + (a^2 + b^2) por cálculo

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + c    ≤ b + c  por h
  _              ≤ b + d por h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c por cálculo
  _              ≤ b + c por h
  _              ≤ b + d por h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c por cálculo
  _              ≤ b + c ya que a ≤ b
  _              ≤ b + d ya que c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c por cálculo
  _              ≤ b + d ya que a ≤ b yy c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c por cálculo
  _              ≤ b + d por h yy h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Calc a + 0 + c = a + c por cálculo
  _              ≤ b + d por h yy h'

def even_fun  (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f g : ℝ → ℝ) : even_fun f → even_fun g →  even_fun (f + g) := by
  intro hf hg
  show ∀ x, (f+g) (-x) = (f+g) x
  intro x₀
  Calc (f + g) (-x₀) = f (-x₀) + g (-x₀) por cálculo
  _                  = f x₀ + g (-x₀)    ya que f (-x₀) = f x₀
  _                  = f x₀ + g x₀       ya que g (-x₀) = g x₀
  _                  = (f + g) x₀        por cálculo

example (f g : ℝ → ℝ) : even_fun f →  even_fun (g ∘ f) := by
  intro hf x
  Calc (g ∘ f) (-x) = g (f (-x)) por cálculo
                _   = g (f x)    ya que f (-x) = f x

example (f : ℝ → ℝ) (x : ℝ) (hx : f (-x) = f x ∧ 1 = 1) : f (-x) + 0 = f x := by
  Calc f (-x) + 0 = f (-x) por cálculo
                _   = f x  ya que f (-x) = f x

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) (x) :  (f+g) (-x) = (f+g) x := by
  Calc (f + g) (-x) = f (-x) + g (-x) por cálculo
  _                 = f x + g (-x)    ya que even_fun f
  _                 = f x + g x       ya que even_fun g
  _                 = (f + g) x       por cálculo

example (ε : ℝ) (h : ε > 1) : 0 ≤ ε := by
  Calc
    (0 : ℝ) ≤ 1 por norm_num
    _       < ε por h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Calc
    (0 : ℝ) ≤ 1 por norm_num
    _       < ε por h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Calc
    ε > 1 por h
    _ > 0 por norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≥ 2 := by
  Calc
    ε + 1 = 1 + 1 usando rw[h]
    _     = 2 por norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≤ 2 := by
  Calc
    ε + 1 = 1 + 1 usando rw [h]
    _     = 2 por norm_num

example (f : ℝ → ℝ) (h : ∀ x, f (f x) = x) : f (f 0) + 0 = 0 := by
  Calc
    f (f 0) + 0 = f (f 0) por cálculo
    _           = 0      por hipótesis

/- example (f : ℝ → ℝ) (h : ∀ x, f (f x) = x) : f (f 0) = 0 + 0 := by
  Calc
    f (f 0) = 0 por hipótesis -/

example (u : ℕ → ℝ) (y) (hy : ∀ n, u n = y) (n m) : u n = u m := by
  Calc
    u n = y ya que ∀ n, u n = y
    _   = u m ya que ∀ n, u n = y

-- Next two examples check casting capabilities

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N > 0 := by
  success_if_fail_with_msg "'calc' expression has type
  3 > 0
but is expected to have type
  N > 0"
    Calc
      3 ≥ 1/ε usando?
      _ > 0 por ε_pos
  Calc
    N ≥ 1/ε por hN
    _ > 0 por ε_pos

-- Combine with relaxed calc now
example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N ≥ 0 := by
  success_if_fail_with_msg "'calc' expression has type
  3 > 0
but is expected to have type
  N ≥ 0"
    Calc
      3 ≥ 1/ε usando?
      _ > 0 por ε_pos
  Calc
    N ≥ 1/ε por hN
    _ > 0 por ε_pos

-- A case where the conclusion has an extra cast
example (N : ℕ) (hN : N ≥ 3) : N > (1 : ℝ) := by
  Calc
    N ≥ 3 por hN
    _ > 1 por cálculo

-- Combine with relaxed calc now
example (N : ℕ) (hN : N ≥ 3) : N ≥ (1 : ℝ) := by
  Calc
    N ≥ 3 por hN
    _ > 1 por cálculo

example (x : ℝ) (p : ℕ) (h : x ≤ p) : x < (p + 1 : ℕ) := by
  Calc x ≤ p por hipótesis
    _ < p + 1 por cálculo

example (u : Nat → Nat) (h : ∀ n, u n = u 0)
  : ∀ n, ∀ m, u m = u n := by
  intro m n
  success_if_fail_with_msg "invalid 'calc' step, left-hand side is
  u m : Nat
but is expected to be
  u n : Nat"
    Calc
      u m = u 0 ya que ∀ n, u n = u 0
      _   = u n ya que ∀ n, u n = u 0
  success_if_fail_with_msg "invalid 'calc' step, right-hand side is
  u n : Nat
but is expected to be
  u m : Nat"
    Calc
      u n = u 0 ya que ∀ n, u n = u 0
      _   = u n ya que ∀ n, u n = u 0
  Calc
    u n = u 0 ya que ∀ n, u n = u 0
    _   = u m ya que ∀ n, u n = u 0
