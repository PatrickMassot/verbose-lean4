import Verbose.Tactics.Since
import Verbose.Tactics.We

section widget
open Lean Server

/-- Parameters for the calc widget. -/
structure VerboseCalcParams extends SelectInsertParams where
  /-- Is this the first calc step? -/
  isFirst : Bool
  /-- indentation level of the calc block. -/
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

end widget

namespace Lean.Elab.Tactic
open Meta Verbose

open Linarith in
def tryLinarithOnly (goal : MVarId) (facts : List Term) : TacticM Bool := do
  let state ← saveState
  goal.withContext do
  let factsE ← facts.mapM (elabTerm ·.raw none)
  try
    linarith true factsE {preprocessors := defaultPreprocessors} goal
    return true
  catch _ =>
    restoreState state
    return false

-- register_endpoint failProvingFacts (goal : Format) : CoreM String

def sinceCalcTac (facts : Array Term) : TacticM Unit := do
  let (newGoal, newFVarsT, newFVars) ← sinceTac facts
  newGoal.withContext do
  tryAll newGoal newFVarsT newFVars
  replaceMainGoal []

def fromRelCalcTac (prfs : Array Term) : TacticM Unit := do
  -- logInfo s!"Running fromRelCalcTact with {prf}"
  evalTactic (← `(tactic| rel [$prfs,*]))

def fromCalcTac (prfs : Array Term) : TacticM Unit := do
  if let #[prf] := prfs then
    concludeTac prf <|> fromRelCalcTac #[prf]
  else
    fromRelCalcTac prfs

elab "fromCalcTac" prfs:term,* : tactic => fromCalcTac prfs

end Lean.Elab.Tactic

section
-- The function mkSelectionPanelRPC from Mathlib is not quite general enough
-- because it allows returning only one suggestion. So we need the following variation.
-- We also use the opportunity to use multilingual support.

open Lean Server SubExpr ProofWidgets SelectInsertParamsClass
open scoped Jsx

register_endpoint theSelectedSubExpr : MetaM String
register_endpoint allSelectedSubExpr : MetaM String
register_endpoint inMainGoal : MetaM String
register_endpoint inMainGoalOrCtx : MetaM String
register_endpoint shouldBe : MetaM String
register_endpoint shouldBePl : MetaM String
register_endpoint selectOnlyOne : MetaM String

abbrev ReplacementSuggestion := String × String × Option (String.Pos × String.Pos)

def mkSelectionPanelRPC' {Params : Type} [SelectInsertParamsClass Params]
    (mkCmdStr : (pos : Array GoalsLocation) → (goalType : Expr) → Params →
   MetaM (Array ReplacementSuggestion))
  (helpMsg : String) (title : String)
  (defaultSuggestions : MetaM (Array ReplacementSuggestion):= pure #[])
  (onlyGoal := true) (onlyOne := false) (extraCss : Option String := none) :
  (params : Params) → RequestM (RequestTask Html) :=
fun params ↦ RequestM.asTask do
let doc ← RequestM.readDoc
let extra := match extraCss with
| some css => <style>{.text css}</style>
| none => .text ""
if h : 0 < (goals params).size then
  let mainGoal := (goals params)[0]
  let mainGoalName := mainGoal.mvarId.name
  mainGoal.ctx.val.runMetaM {} do
  let md ← mainGoal.mvarId.getDecl
  let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
  Meta.withLCtx lctx md.localInstances do
  let defaultSuggestions ← defaultSuggestions
  let all ← if onlyOne then theSelectedSubExpr else allSelectedSubExpr
  let be_where ← if onlyGoal then inMainGoal else inMainGoalOrCtx
  let errorMsg := s!"{all} {← if onlyOne then shouldBe else shouldBePl} {be_where}"
  let inner : Html ← (do
    if onlyOne && (selectedLocations params).size > 1 then
      return <span>{.text (← selectOnlyOne)}</span>
    for selectedLocation in selectedLocations params do
      if selectedLocation.mvarId.name != mainGoalName then
        return <span>{.text errorMsg}</span>
      else if onlyGoal then
        if !(selectedLocation.loc matches (.target _)) then
          return <span>{.text errorMsg}</span>
    if (selectedLocations params).isEmpty && defaultSuggestions.isEmpty then
        return .text ""
    let mut suggestions : Array Html := #[]
    for (linkText, newCode, range?) in
        defaultSuggestions ++
        (← mkCmdStr (selectedLocations params) md.type.consumeMData params) do
      suggestions := suggestions.push <| Html.ofComponent
        MakeEditLink
        (.ofReplaceRange doc.meta (replaceRange params) newCode range?)
        #[ .text linkText ]
    pure (.element "ul" #[("style", json% { "font-size": "125%"})] <| suggestions.map fun s ↦ <li>{s}</li>))
  return <details «open»={true}>
      <summary className="mv2 pointer">{.text title}</summary>
      <div className="ml1"><p>{.text helpMsg}</p>{inner}</div>
      {extra}
    </details>
else
  return extra -- This shouldn't happen.

end

section widget

open ProofWidgets Lean Meta

register_endpoint getSince? : MetaM String
register_endpoint createOneStepMsg : MetaM String
register_endpoint createTwoStepsMsg : MetaM String

/-- Return the link text and inserted text above and below of the calc widget. -/
def verboseSuggestSteps (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams) :
    MetaM (Array ReplacementSuggestion) := do
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

  let since? ← getSince?
  let spc := String.replicate params.indent ' '
  let insertedCode := match isSelectedLeft, isSelectedRight with
  | true, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} {since?}\n{spc}_ {relStr} {newRhsStr} {since?}\n\
         {spc}_ {relStr} {rhsStr} {since?}"
    else
      s!"_ {relStr} {newLhsStr} {since?}\n{spc}\
         _ {relStr} {newRhsStr} {since?}\n{spc}\
         _ {relStr} {rhsStr} {since?}"
  | false, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newRhsStr} {since?}\n{spc}_ {relStr} {rhsStr} {since?}"
    else
      s!"_ {relStr} {newRhsStr} {since?}\n{spc}_ {relStr} {rhsStr} {since?}"
  | true, false =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} {since?}\n{spc}_ {relStr} {rhsStr} {since?}"
    else
      s!"_ {relStr} {newLhsStr} {since?}\n{spc}_ {relStr} {rhsStr} {since?}"
  | false, false => "This should not happen"

  let stepInfo ← match isSelectedLeft, isSelectedRight with
  | true, true => createTwoStepsMsg
  | true, false | false, true => createOneStepMsg
  | false, false => pure "This should not happen"
  let pos : String.Pos := insertedCode.find (fun c => c == '?')
  return #[(stepInfo, insertedCode, some (pos, ⟨pos.byteIdx + 2⟩) )]

open Lean.SubExpr in
/-- Given a `Array GoalsLocation` return the array of `SubExpr.Pos` for all locations
in the targets of the relevant goals. -/
def getSelectedFVars (locations : Array GoalsLocation) : Array FVarId := Id.run do
  let mut res : Array FVarId := #[]
  for location in locations do
    if let .hyp fvar := location.loc then
      res := res.push fvar
    if let .hypType fvar pos := location.loc then
      if pos.isRoot then
        res := res.push fvar
  return res

register_endpoint mkSinceCalcTac : MetaM String
register_endpoint mkSinceCalcHeader : MetaM String
register_endpoint mkSinceCalcArgs (args : Array Format) : MetaM String

register_endpoint mkComputeCalcTac : MetaM String
register_endpoint mkComputeCalcDescr : MetaM String
register_endpoint mkComputeAssptTac : MetaM String
register_endpoint mkComputeAssptDescr : MetaM String

def verboseGetDefaultCalcSuggestions : MetaM (Array ReplacementSuggestion) := do
  let nope : Option (String.Pos × String.Pos) := none
  return #[(← mkComputeCalcDescr, ← mkComputeCalcTac, nope),
           (← mkComputeAssptDescr, ← mkComputeAssptTac, nope)]

/-- Return the link text and inserted text above and below of the calc widget. -/
def verboseSelectSince (pos : Array Lean.SubExpr.GoalsLocation) (_goalType : Expr)
    (_params : CalcParams) :
    MetaM (Array <| String × String × Option (String.Pos × String.Pos)) := do
  let fvars := getSelectedFVars pos
  let justifications ← fvars.mapM (FVarId.getType · >>= PrettyPrinter.ppExpr)
  let justifStr ← mkSinceCalcArgs justifications
  if justifStr == "" then
    return #[]
  else
    return #[(s!"{← mkSinceCalcHeader} {justifStr}", s!"{← mkSinceCalcTac} {justifStr}", none)]

abbrev calcSuggestionProviderFun := (pos : Array Lean.SubExpr.GoalsLocation) → (goalType : Expr) →
    (params : CalcParams) →
    MetaM (Array <| String × String × Option (String.Pos × String.Pos))

def getCalcSuggestion : calcSuggestionProviderFun := fun pos goalType params ↦ do
  let conf ← verboseConfigurationExt.get
  let provider := conf.calcSuggestionProvider
  let env ← getEnv
  if env.find? provider matches none then
    throwError s!"Could not find calc suggestion provider '{provider}'"
  match unsafe env.evalConst calcSuggestionProviderFun {} provider with
  | .ok res => res pos goalType params
  | _ =>
    throwError s!"Could not find calc suggestion provider '{provider}'"



end widget

open Lean Elab Tactic in
def mkCalc?Tac (title calcTac since?tac : String) : TacticM Unit := withMainContext do
  let goalFmt ← Meta.ppExpr (← getMainTarget)
  let s := s!"{calcTac} {goalFmt} {since?tac}"
  Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) #[.suggestion s] (header := title)
  evalTactic (← `(tactic|sorry))

namespace Lean.Elab.Tactic
open Meta

/-- Elaborator for the `calc` tactic mode variant. Mostly from core Lean but
also try to apply `le_of_lt`, `Eq.le` or `Eq.ge`. -/
def evalVerboseCalc : Tactic
  | `(tactic| calc%$tk $steps:calcSteps) =>
    withRef tk do
    closeMainGoalUsing `calc (checkNewUnassigned := false) fun target tag => do
    withTacticInfoContext steps do
      let steps ← Term.mkCalcStepViews steps
      let target := (← instantiateMVars target).consumeMData
      let (val, mvarIds) ← withCollectingNewGoalsFrom (parentTag := tag) (tagSuffix := `calc) <| runTermElab do
        let (val, valType) ← Term.elabCalcSteps steps
        if (← isDefEq valType target) then
          -- Immediately the right type, no need for further processing.
          return val

        let some (ev, lhs, rhs) ← Term.getCalcRelation? valType | unreachable!
        if let some (er, elhs, erhs) ← Term.getCalcRelation? target then
          -- If the goal is an inequality and we prove a strict inequality, try to deduce
          -- the inequality using `le_of_lt`.

          if (← verboseConfigurationExt.get).useRelaxedCalc then
            if er.isAppOf `LE.le && ev.isAppOf `LT.lt then
              if ← isDefEq lhs elhs <&&> isDefEq rhs erhs then
              return ← mkAppM `le_of_lt #[val]
            else if er.isAppOf `GE.ge && ev.isAppOf `GT.gt then
              if ← isDefEq lhs elhs <&&> isDefEq rhs erhs then
              return ← mkAppM `le_of_lt #[val]
            else if er.isAppOf `LE.le && ev.isAppOf `GT.gt then
              if ← isDefEq lhs erhs <&&> isDefEq rhs elhs then
              return ← mkAppM `le_of_lt #[val]
            else if er.isAppOf `GE.ge && ev.isAppOf `LT.lt then
              if ← isDefEq lhs erhs <&&> isDefEq rhs elhs then
              return ← mkAppM `le_of_lt #[val]
            -- If the goal is an inequality and we prove an equality, try to deduce
            -- the inequality using `Eq.le` or `Eq.ge`.
            else if er.isAppOf `LE.le && ev.isAppOf `Eq then
              if ← isDefEq lhs elhs <&&> isDefEq rhs erhs then
                return ← mkAppM `Eq.le #[val]
              else if ← isDefEq lhs erhs <&&> isDefEq rhs elhs then
                return ← mkAppM `Eq.ge #[val]
            else if er.isAppOf `GE.ge && ev.isAppOf `Eq then
              if ← isDefEq lhs elhs <&&> isDefEq rhs erhs then
                return ← mkAppM `Eq.ge #[val]
              else if ← isDefEq lhs erhs <&&> isDefEq rhs elhs then
                return ← mkAppM `Eq.le #[val]
          -- Feature: if the goal is `x ~ y`, try extending the `calc` with `_ ~ y` with a new "last step" goal.
          if ← isDefEq lhs elhs <&&> isDefEq (← inferType rhs) (← inferType elhs) then
            let lastStep := mkApp2 er rhs erhs
            let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
            try
              let (val', valType') ← Term.mkCalcTrans val valType lastStepGoal lastStep
              if (← isDefEq valType' target) then
                return val'
            catch _ =>
              pure ()

        -- Calc extension failed, so let's go back and mimick the `calc` expression
        Term.ensureHasTypeWithErrorMsgs target val
          (mkImmedErrorMsg := fun _ => Term.throwCalcFailure steps)
          (mkErrorMsg := fun _ => Term.throwCalcFailure steps)
      pushGoals mvarIds
      return val
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
