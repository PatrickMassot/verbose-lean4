import Verbose.Tactics.Widget
import Verbose.English.Help

namespace Verbose.English
open Lean Meta Server

open ProofWidgets

def mkMaybeApp (selectedForallME : MyExpr) (selectedForallIdent : Ident) (data : Expr) :
    MetaM (TSyntax `maybeApplied) := do
  let dataS ← PrettyPrinter.delab data
  match selectedForallME with
  | .forall_simple e _v _t prop => do
    match prop with
    | .impl ..=> do
      let leS ← PrettyPrinter.delab (e.bindingBody!.bindingDomain!.instantiate1 data)
      `(maybeApplied|$selectedForallIdent:term applied to $dataS:term using that $leS)
    | _ => `(maybeApplied|$selectedForallIdent:term applied to $dataS:term)
  | .forall_rel _ _ _ rel rhs _ => do
    let relS ← mkRelStx' data rel rhs
    `(maybeApplied|$selectedForallIdent:term applied to $dataS:term using that $relS)
  | _ => unreachable!

def mkNewStuff (selectedForallME : MyExpr) (selectedForallType : Expr) (data : Expr) (goal : MVarId)
    (newsIdent : Ident) : MetaM (Expr × TSyntax `newStuffEN) := do
  let obtained := match selectedForallME with
    | .forall_simple _ _ _ prop =>
      match prop with
      | .impl .. => selectedForallType.bindingBody!.bindingBody!.instantiate1 data
      | _ => selectedForallType.bindingBody!.instantiate1 data
    | .forall_rel _ _ _ _ _ _ => selectedForallType.bindingBody!.bindingBody!.instantiate1 data
    | _ => unreachable!

  let newS ← parse obtained fun obtainedME ↦ do
    match obtainedME with
    | .exist_simple _e v _t propo => do
      let vN ← goal.getUnusedUserName v
      let vS := mkIdent vN
      let hS := mkIdent (← goal.getUnusedUserName ("h"++ toString vN : String))
      withRenamedFVar v vN do
      let obtainedS ← PrettyPrinter.delab (propo.toExpr.instantiate1 data)
      `(newStuffEN|$vS:ident such that $hS:ident : $obtainedS:term)
    | .exist_rel _e v _t rel rel_rhs propo => do
      let vN ← goal.getUnusedUserName v
      let vS := mkIdent vN
      let relI := mkIdent s!"{v}{symb_to_hyp rel rel_rhs}"
      let relS ← mkRelStx vN rel rel_rhs
      let hS := mkIdent (← goal.getUnusedUserName ("h"++ toString vN : String))
      withRenamedFVar v vN do
      let obtainedS ← PrettyPrinter.delab (propo.toExpr.instantiate1 data)
      `(newStuffEN|$vS:ident such that ($relI : $relS) ($hS:ident : $obtainedS:term))
    | _ => do
      let obtainedS ← PrettyPrinter.delab (obtained.instantiate1 data)
      `(newStuffEN|$newsIdent:ident : $obtainedS:term)
  return (obtained, newS)

def mkUnfoldSuggestion (selected : Array SubExpr.GoalsLocation) (goal : MVarId) (debug : Bool) : MetaM (Array SuggestionInfo) := do
  if h : selected.size ≠ 1 then
   return if debug then #[⟨"more than one selection", "", none⟩] else #[]
  else
    have : 0 < selected.size := by rw [not_not] at h; simp [h]
    let sel := selected[0]
    unless sel.mvarId.name = goal.name do return if debug then
      #[⟨s!"Not the right goal: {sel.mvarId.name} vs {goal.name}", "", none⟩] else #[]
    goal.withContext do
    let ctx ← getLCtx
    match sel.loc with
    | .hyp fvarId => do
      let ld := ctx.get! fvarId
      unless ← ld.type.isAppFnUnfoldable do
        return if debug then #[⟨"Could not expand", "", none⟩] else #[]
      if let some e ← ld.type.expandHeadFun then
        let hI := mkIdent ld.userName
        let eS ← PrettyPrinter.delab e
        let s ← toString <$> PrettyPrinter.ppTactic (← `(tactic|We reformulate $hI as $eS))
        return #[⟨s, s ++ "\n  ", none⟩]
      else
        return if debug then #[⟨"Could not expand", "", none⟩] else #[]
    | .hypType fvarId pos => do
      let ld := ctx.get! fvarId
      unless ← ld.type.isAppFnUnfoldable do
        return if debug then #[⟨"Could not expand def in a value", "", none⟩] else #[]
      try
        let expanded ← replaceSubexpr Lean.Expr.expandHeadFun! pos ld.type
        let hI := mkIdent ld.userName
        let eS ← PrettyPrinter.delab expanded
        let s ← toString <$> PrettyPrinter.ppTactic (← `(tactic|We reformulate $hI as $eS))
        return #[⟨s, s ++ "\n  ", none⟩]
      catch _ => return if debug then #[⟨"Could not expand", "", none⟩] else #[]
    | .hypValue .. => return if debug then #[⟨"Cannot expand def in a value", "", none⟩] else #[]
    | .target pos => do
      let goalType ← goal.getType
      unless ← goalType.isAppFnUnfoldable do
        return if debug then #[⟨"Could not expand", "", none⟩] else #[]
      try
        let expanded ← replaceSubexpr Lean.Expr.expandHeadFun! pos goalType
        let eS ← PrettyPrinter.delab expanded
        let s ← toString <$> PrettyPrinter.ppTactic (←  `(tactic|Let's prove that $eS))
        return #[⟨s, s ++ "\n  ", none⟩]
      catch _ => return if debug then #[⟨"Could not expand", "", none⟩] else #[]


def makeSuggestionsOnlyLocal (selectionInfo : SelectionInfo) (goal : MVarId) (debug : Bool) :
    MetaM (Array SuggestionInfo) := do
  let forallFVars ← selectionInfo.forallFVars
  match forallFVars with
  | #[selectedForallDecl] => do
    let selectedForallType ← whnf selectedForallDecl.type
    let selectedForallIdent := mkIdent selectedForallDecl.userName
    -- We will try specializing the selected forall to each element of `datas`.
    let datas ← selectionInfo.mkData selectedForallType.bindingDomain!
    let newsIdent := mkIdent (← goal.getUnusedUserName `H)
    parse selectedForallType fun selectedForallME ↦ do
    let mut sugs := #[]
    for data in datas do
      let maybeApp ← mkMaybeApp selectedForallME selectedForallIdent data

      let (obtained, newStuffEN) ← mkNewStuff selectedForallME selectedForallType data goal newsIdent
      let tac ← if ← isDefEq (obtained.instantiate1 data) (← goal.getType) then
        `(tactic|We conclude by $maybeApp:maybeApplied)
      else
        `(tactic|By $maybeApp:maybeApplied we get $newStuffEN)
      sugs := sugs.push (← toString <$> PrettyPrinter.ppTactic tac)
    if sugs.isEmpty then
      return if debug then #[⟨s!"Bouh typStr: {← ppExpr selectedForallType.bindingDomain!}, si.dataFVars: {selectionInfo.dataFVars}, datas: {← datas.mapM ppExpr}", "", none⟩] else #[]
    return sugs.map fun x ↦ ⟨x, x ++ "\n  ", none⟩
  | _ => return if debug then #[⟨s!"Only local decls : {forallFVars.map (fun l ↦ l.userName)}", "", none⟩] else #[]

def makeSuggestions (selectionInfo : SelectionInfo) (goal : MVarId) (selected : Array SubExpr.GoalsLocation) :
    MetaM (Array SuggestionInfo) :=
  withoutModifyingState do
  let debug := (← getOptions).getBool `verbose.suggestion_debug
  if selectionInfo.onlyFullGoal then
    let (s, _msg) ← gatherSuggestions (helpAtGoal goal)
    return ← s.mapM fun sug ↦ do
      let text ← sug.suggestion.pretty
      pure ⟨toString text, toString text ++ "\n  ", none⟩
  if let some ld := selectionInfo.singleProp then
    let (s, _msg) ← gatherSuggestions (helpAtHyp goal ld.userName)
    return ← s.mapM fun sug ↦ do
      let text ← sug.suggestion.pretty
      pure ⟨toString text, toString text ++ "\n  ", none⟩
  let unfoldSuggestions ← mkUnfoldSuggestion selected goal debug
  if selectionInfo.fullGoal then
    parse (← goal.getType) fun goalME ↦ do
    match goalME with
    | .exist_simple e _ typ _ | .exist_rel e _ typ .. => do
      let wits ← selectionInfo.mkData typ
      let mut sugs := #[]
      for wit in wits do
        let witS ← PrettyPrinter.delab wit
        sugs := sugs.push (← do
        let newGoal ← PrettyPrinter.delab (e.getAppArgs'[1]!.bindingBody!.instantiate1 wit)
        let tac ← `(tactic|Let's prove that $witS works : $newGoal)
        toString <$> (PrettyPrinter.ppTactic tac))
      return unfoldSuggestions ++ sugs.map fun x ↦ ⟨x, x ++ "\n  ", none⟩
    | _ => return if debug then #[⟨"fullGoal not exist", "", none⟩] else #[]
  else if selectionInfo.onlyLocalDecls then
    return unfoldSuggestions ++ (← makeSuggestionsOnlyLocal selectionInfo goal debug)
  else
    return unfoldSuggestions ++ if debug then #[⟨"bottom", "", none⟩] else #[]


@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Use shift-click to select sub-expressions."
  "Suggestions"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx@`(tactic| with_suggestions $seq) => do
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx
    Lean.Elab.Tactic.evalTacticSeq seq
  | _ => Lean.Elab.throwUnsupportedSyntax
