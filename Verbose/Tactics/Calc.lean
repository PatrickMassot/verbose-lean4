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
  trySolveByElimAnonFactSplitCClinRel newGoal newFVarsT newFVars
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

section widget

open ProofWidgets Lean Meta

register_endpoint getSince? : MetaM String
register_endpoint createOneStepMsg : MetaM String
register_endpoint createTwoStepsMsg : MetaM String

/-- Return the link text and inserted text above and below of the calc widget. -/
def verboseSuggestSteps (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams) :
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
  return (stepInfo, insertedCode, some (pos, ⟨pos.byteIdx + 2⟩) )

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

/-- Return the link text and inserted text above and below of the calc widget. -/
def verboseSelectSince (pos : Array Lean.SubExpr.GoalsLocation) (_goalType : Expr)
    (_params : CalcParams) :
    MetaM (String × String × Option (String.Pos × String.Pos)) := do
  let fvars := getSelectedFVars pos
  let justifications ← fvars.mapM (FVarId.getType · >>= PrettyPrinter.ppExpr)
  let justifStr ← mkSinceCalcArgs justifications
  if justifStr == "" then
    return ("", "", none)
  else
    return (s!"{← mkSinceCalcHeader} {justifStr}", s!"{← mkSinceCalcTac} {justifStr}", none)

abbrev calcSuggestionProviderFun := (pos : Array Lean.SubExpr.GoalsLocation) → (goalType : Expr) →
    (params : CalcParams) →
    MetaM (String × String × Option (String.Pos × String.Pos))

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
