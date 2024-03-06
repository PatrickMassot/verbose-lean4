import Verbose.Infrastructure.Initialize
import Verbose.Tactics.Help
import Verbose.Infrastructure.Extension

/-! # Suggestion widget infrastructure

This file provides foundations for the suggestion widget. Unfortunately there remains of lot of code that
is duplicated among the language folders since the widget really mixes analyzing selected items and
building tactic syntax.

The first piece of infrastructure is a way to reorganize the selection information.
When user select subexpressions in the InfoView, Lean core provides a list of subexpressions
where each item mentions whether the subexpression is a goal or the name of a local context item
or inside the type of such an item or inside the value of such an item.

The `SelectionInfo` data structure is presenting the same information but from another
perspective, grouping the selections by kind instead of providing a flat list where
each item has a kind information. The function that turns such a list into a `SelectionInfo`
is `mkSelectionInfos` (more precisly it produces a `HashMap` of those indexed by the goals
`MVarId`s). Then a number of function consume this data to answer
various questions about what is selected.

The next piece is made of data generators. For instance is the user select a number `ε`
then the suggestion widget may propose to specialize a universal quantifier with
`ε` but also `ε/2`. If two numbers `ε` and `δ` are selected then the generated data
will include `min ε δ`, `max ε δ` etc... Currently this is not extensible or modifyable
by library users but it should be.

Finally this file also contains the suggestion widget code. Of course this code takes as
parameter a function that turn selection informations into actual suggestions. Defining
such a function is done in the languages folders (and this is where there code duplication).
-/




open Lean Meta Server

open ProofWidgets

section



/-! ## Data generators -/

/- FIXME: the function below is a stupid lazy way of creating an expression. -/
def mkHalf (e typ : Expr) : MetaM Expr := do
  let main : Elab.TermElabM Expr := do
    let baseS ← PrettyPrinter.delab e
    Lean.Elab.Term.elabTerm (← `($baseS/2)) typ
  main.run'

/- FIXME: the function below is a stupid lazy way of creating an expression. -/
def mkAddOne (e typ : Expr) : MetaM Expr := do
  let main : Elab.TermElabM Expr := do
    let baseS ← PrettyPrinter.delab e
    Lean.Elab.Term.elabTerm (← `($baseS + 1)) typ
  main.run'

/- FIXME: the function below is a stupid lazy way of creating an expression. -/
def mkMin (e e' typ : Expr) : MetaM Expr := do
  let main : Elab.TermElabM Expr := do
    let baseS ← PrettyPrinter.delab e
    let baseS' ← PrettyPrinter.delab e'
    Lean.Elab.Term.elabTerm (← `(min $baseS $baseS')) typ
  main.run'

/- FIXME: the function below is a stupid lazy way of creating an expression. -/
def mkMax (e e' typ : Expr) : MetaM Expr := do
  let main : Elab.TermElabM Expr := do
    let baseS ← PrettyPrinter.delab e
    let baseS' ← PrettyPrinter.delab e'
    Lean.Elab.Term.elabTerm (← `(max $baseS $baseS')) typ
  main.run'

/- FIXME: the function below is a stupid lazy way of creating an expression. -/
def mkAdd (e e' typ : Expr) : MetaM Expr := do
  let main : Elab.TermElabM Expr := do
    let baseS ← PrettyPrinter.delab e
    let baseS' ← PrettyPrinter.delab e'
    Lean.Elab.Term.elabTerm (← `($baseS + $baseS')) typ
  main.run'

def SelectionInfo.mkBasicData (si : SelectionInfo) (typ : Expr) : MetaM (Array Expr) := do
  let typStr := toString (← ppExpr typ)
  let some decls := si.dataFVars[typStr] | return #[]
  match decls with
  | #[d] => do
    let e := d.toExpr
    return #[e, ← mkHalf e typ, ← mkAddOne e typ]
  | #[d, d'] => do
    let e := d.toExpr
    let e' := d'.toExpr
    return #[← mkMin e e' typ, ← mkMax e e' typ, ← mkAdd e e' typ]
  | _ => return #[]

def SelectionInfo.mkData (si : SelectionInfo) (typ : Expr) : MetaM (Array Expr) := do
  let typStr := toString (← ppExpr typ)
  let mut res ← si.mkBasicData typ
  for (key, value) in si.dataFVars.toList do
    if key.endsWith s!" → {typStr}" then
      for decl in value do
        for arg in ← si.mkBasicData decl.type.bindingDomain! do
          res := res.push (.app decl.toExpr arg)
  return res

end

/-! ## The suggestion widget -/


def List.pushIfNew {α : Type*} [BEq α] (a : α) : List α → List α
| h::t => if h == a then h::t else h::(pushIfNew a t)
| [] => [a]

def Array.pushIfNew {α : Type*} [BEq α] (as : Array α) (a : α) : Array α :=
(as.toList.pushIfNew a).toArray

structure SuggestionsParams where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : Array SubExpr.GoalsLocation
  deriving RpcEncodable



open scoped Jsx in open Lean.SubExpr in
def mkPanelRPC
    (mkCmdStr : (selectionInfo : SelectionInfo) → (goal : MVarId) → WidgetM Unit)
  (helpMsg : String) (title : String) (onlyGoal := false) (onlyOne := false) :
  (params : SuggestionsParams) → RequestM (RequestTask Html) :=
fun params ↦ RequestM.asTask do
let doc ← RequestM.readDoc
if h : 0 < params.goals.size then
  let mainGoal := params.goals[0]
  let mainGoalName := mainGoal.mvarId.name
  let all := if onlyOne then "The selected sub-expression" else "All selected sub-expressions"
  let be_where := if onlyGoal then "in the main goal." else "in the main goal or its context."
  let errorMsg := s!"{all} should be {be_where}"
  let inner : Html ← (do
    if onlyOne && params.selectedLocations.size > 1 then
      return <span>{.text "You should select only one sub-expression"}</span>
    for selectedLocation in params.selectedLocations do
      if selectedLocation.mvarId.name != mainGoalName then
        return <span>{.text errorMsg}</span>
      else if onlyGoal then
        if !(selectedLocation.loc matches (.target _)) then
          return <span>{.text errorMsg}</span>
    if params.selectedLocations.isEmpty then
      return <span>{.text helpMsg}</span>
    mainGoal.ctx.val.runMetaM {} do
      let md ← mainGoal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        let selections ← mkSelectionInfos params.selectedLocations
        let curIndent := params.pos.character
        let (_, suggestions) ← (mkCmdStr selections[mainGoal.mvarId].get! mainGoal.mvarId).run default
        let mut children : Array Html := #[]
        for suggs in [suggestions.suggestionsPre, suggestions.suggestionsMain, suggestions.suggestionsPost] do
          for ⟨linkText, newCode, range?⟩ in suggs do
            children := children.push <| Html.element "li" #[("style", json% {"margin-bottom": "1rem"})] #[.ofComponent
              MakeEditLink
              (.ofReplaceRange doc.meta ⟨params.pos, params.pos⟩ (ppAndIndentNewLine curIndent newCode) range?)
              #[ .text linkText ]]


        return Html.element "ul" #[("style", json% { "font-size": "150%"})] children)
  return <details «open»={true}>
      <summary className="mv2 pointer">{.text title}</summary>
      <div className="ml1">{inner}</div>
    </details>
else
  return <span>{.text "There is no goal to solve!"}</span> -- This shouldn't happen.

/-! ## Debugging instances -/

instance : Inhabited SubExpr.GoalLocation := ⟨.target SubExpr.Pos.root⟩

instance : ToString LocalDecl := ⟨toString ∘ LocalDecl.userName⟩

instance {α β : Type} [BEq α] [Hashable α] [ToString α] [ToString β] : ToString (Std.HashMap α β) :=
⟨fun m ↦ "\n".intercalate <| m.toList.map fun p : α × β ↦ s!"{p.1} : {p.2}"⟩

/-! ## Suggestion making -/

open Verbose

def mkNewStuff (selectedForallME : MyExpr) (selectedForallType : Expr) (data : Expr) (goal : MVarId)
    (newsIdent : Ident) : MetaM (Expr × List MaybeTypedIdent) := do
  let obtained := match selectedForallME with
    | .forall_simple _ _ _ prop =>
      match prop with
      | .impl .. => selectedForallType.bindingBody!.bindingBody!.instantiate1 data
      | _ => selectedForallType.bindingBody!.instantiate1 data
    | .forall_rel _ _ _ _ _ _ => selectedForallType.bindingBody!.bindingBody!.instantiate1 data
    | _ => unreachable!

  let newS : List MaybeTypedIdent ← parse obtained fun obtainedME ↦ do
    match obtainedME with
    | .exist_simple _e v _t propo => do
      let vN ← goal.getUnusedUserName v
      let hN ← goal.getUnusedUserName ("h"++ toString vN : String)
      withRenamedFVar v vN do
      let obtainedS ← PrettyPrinter.delab (propo.toExpr.instantiate1 data)
      pure [(vN, none), (hN, obtainedS)]
    | .exist_rel _e v _t rel rel_rhs propo => do
      let vN ← goal.getUnusedUserName v
      let relN : Name := s!"{v}{symb_to_hyp rel rel_rhs}"
      let relS ← mkRelStx vN rel rel_rhs
      let hN ← goal.getUnusedUserName ("h"++ toString vN : String)
      withRenamedFVar v vN do
      let obtainedS ← PrettyPrinter.delab (propo.toExpr.instantiate1 data)
      pure [(vN, none), (relN, some relS), (hN, obtainedS)]
    | _ => do
      let obtainedS ← PrettyPrinter.delab (obtained.instantiate1 data)
      pure [(newsIdent.getId, some obtainedS)]
  return (obtained, newS)

endpoint mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic)

endpoint mkShowTacStx (new : Term) : MetaM (TSyntax `tactic)

def mkUnfoldSuggestion (selectionInfo : SelectionInfo) (goal : MVarId) :
    WidgetM Unit :=
  do
  let selected := selectionInfo.selected
  if h : selected.size ≠ 1 then
    debugMessage "more than one selection"
  else
    have : 0 < selected.size := by rw [not_not] at h; simp [h]
    let sel := selected[0]
    unless sel.mvarId.name = goal.name do
      debugMessage s!"Not the right goal: {sel.mvarId.name} vs {goal.name}"
      return
    goal.withContext do
    let ctx ← getLCtx
    match sel.loc with
    | .hyp fvarId => do
      let ld := ctx.get! fvarId
      unless ← ld.type.isAppFnUnfoldable do
        debugMessage "Could not expand"
        return
      if let some e ← ld.type.expandHeadFun then
        let hI := mkIdent ld.userName
        let eS ← PrettyPrinter.delab e
        let s ← toString <$> PrettyPrinter.ppTactic (← mkReformulateHypTacStx hI eS)
        pushPreSuggestion s
      else
        debugMessage "Could not expand" ; return
    | .hypType fvarId pos => do
      let ld := ctx.get! fvarId
      unless ← ld.type.isAppFnUnfoldable do
        debugMessage "Could not expand def in a value" ; return
      try
        let expanded ← liftM <| replaceSubexpr Lean.Expr.expandHeadFun! pos ld.type
        let hI := mkIdent ld.userName
        let eS ← PrettyPrinter.delab expanded
        let s ← toString <$> PrettyPrinter.ppTactic (← mkReformulateHypTacStx hI eS)
        pushPreSuggestion s ; return
      catch _ => debugMessage "Could not expand" ; return
    | .hypValue .. => debugMessage "Cannot expand def in a value" ; return
    | .target pos => do
      let goalType ← goal.getType
      unless ← goalType.isAppFnUnfoldable do
        debugMessage "Could not expand" ; return
      try
        let expanded ← liftM <| replaceSubexpr Lean.Expr.expandHeadFun! pos goalType
        let eS ← PrettyPrinter.delab expanded
        let s ← toString <$> PrettyPrinter.ppTactic (← mkShowTacStx eS)
        pushPreSuggestion s ; return
      catch _ => debugMessage "Could not expand" ; return


endpoint mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic)

endpoint mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic)

def mkMaybeApp (selectedForallME : MyExpr) (selectedForallIdent : Ident) (data : Expr) :
    MetaM (List Term) := do
  let dataS ← PrettyPrinter.delab data
  match selectedForallME with
  | .forall_simple e _v _t prop => do
    match prop with
    | .impl ..=> do
      let leS ← PrettyPrinter.delab (e.bindingBody!.bindingDomain!.instantiate1 data)
      return [selectedForallIdent, dataS, leS]
    | _ => return [selectedForallIdent, dataS]
  | .forall_rel _ _ _ rel rhs _ => do
    let relS ← mkRelStx' data rel rhs
    return [selectedForallIdent, dataS, relS]
  | _ => unreachable!

def makeSuggestionsOnlyLocal (selectionInfo : SelectionInfo) (goal : MVarId) :
    WidgetM Unit := do
  if selectionInfo.onlyLocalDecls then do
  let forallFVars ← selectionInfo.forallFVars
  match forallFVars with
  | #[selectedForallDecl] => do
    let selectedForallType ← whnf selectedForallDecl.type
    let selectedForallIdent := mkIdent selectedForallDecl.userName
    -- We will try specializing the selected forall to each element of `datas`.
    let datas ← selectionInfo.mkData selectedForallType.bindingDomain!
    let newsIdent := mkIdent (← goal.getUnusedUserName `H)
    parse selectedForallType fun selectedForallME ↦ do
    for data in datas do
      let maybeAppTerms ← mkMaybeApp selectedForallME selectedForallIdent data
      let (obtained, newStuff) ← mkNewStuff selectedForallME selectedForallType data goal newsIdent
      let tac ← if ← isDefEq (obtained.instantiate1 data) (← goal.getType) then
        mkConcludeTacStx maybeAppTerms
      else
        mkObtainTacStx maybeAppTerms newStuff
      pushSuggestion (← toString <$> PrettyPrinter.ppTactic tac)
    if datas.isEmpty then
      debugMessage s!"Bouh typStr: {← liftM $ ppExpr selectedForallType.bindingDomain!}, si.dataFVars: {selectionInfo.dataFVars}, datas: {← liftM $ datas.mapM ppExpr}"
  | _ => debugMessage s!"Only local decls : {forallFVars.map (fun l ↦ l.userName)}"

endpoint mkUseTacStx (wit : Term) (newGoal : Option Term) : MetaM (TSyntax `tactic)

endpoint mkSinceTacStx (facts : Array Term) (concl : Term) : MetaM (TSyntax `tactic)

def makeSuggestionsOnlyFullGoals (selectionInfo : SelectionInfo) (goal : MVarId) : WidgetM Unit := do
  if selectionInfo.onlyFullGoal then do
  let (s, _msg) ← gatherSuggestions (helpAtGoal goal)
  for sug in s do
    let text ← sug.suggestion.pretty
    pushSuggestion (toString text)

def makeSuggestionsSingleProp (selectionInfo : SelectionInfo) (goal : MVarId) : WidgetM Unit := do
  let some ld := selectionInfo.singleProp | return
  let (s, _msg) ← gatherSuggestions (helpAtHyp goal ld.userName)
  for sug in s do
    let text ← sug.suggestion.pretty
    pushSuggestion (toString text)

def makeSuggestionsFullGoal (selectionInfo : SelectionInfo) (goal : MVarId) : WidgetM Unit := do
  if selectionInfo.fullGoal then do
  parse (← goal.getType) fun goalME ↦ do
  match goalME with
  | .exist_simple e _ typ _ | .exist_rel e _ typ .. => do
    for wit in ← selectionInfo.mkData typ do
      let witS ← PrettyPrinter.delab wit
      let newGoal ← PrettyPrinter.delab (e.getAppArgs'[1]!.bindingBody!.instantiate1 wit)
      let tac ← mkUseTacStx witS (some newGoal)
      pushSuggestion (← toString <$> (PrettyPrinter.ppTactic tac))
  | _ => do
    if selectionInfo.dataFVars.isEmpty && 0 < selectionInfo.propFVars.size && selectionInfo.propFVars.size ≤ 4  then
      let goalS ← PrettyPrinter.delab (← goal.getType)
      let propsS ← selectionInfo.propFVars.mapM fun ld ↦ PrettyPrinter.delab ld.type
      let tac ← PrettyPrinter.ppTactic (← mkSinceTacStx propsS goalS)
      pushSuggestion (toString tac)
    else
      debugMessage "fullGoal not exist"

def makeSuggestions (selectionInfo : SelectionInfo) (goal : MVarId) : WidgetM Unit :=
  withoutModifyingState
  for provider in ← Verbose.getSuggestionsProviders do
    provider selectionInfo goal

set_option hygiene false in
macro "useDefaultSuggestionProviders" : command =>
`(configureSuggestionProviders mkUnfoldSuggestion
                               makeSuggestionsOnlyFullGoals
                               makeSuggestionsSingleProp
                               makeSuggestionsFullGoal
                               makeSuggestionsOnlyLocal)
