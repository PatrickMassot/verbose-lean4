import Verbose.Tactics.Help
import Verbose.Infrastructure.Extension

/-! # Suggestion widget infrastructure

This file provides foundations for the suggestion widget.

It builds on the `SelectionInfo` infrastructure.
The first piece defined here is data generators. For instance is the user select a number `ε`
then the suggestion widget may propose to specialize a universal quantifier with
`ε` but also `ε/2`. If two numbers `ε` and `δ` are selected then the generated data
will include `min ε δ`, `max ε δ` etc... Currently this is not extensible or modifyable
by library users but it should be.

Finally this file also contains the suggestion widget code. Of course this code takes as
parameter a function that turn selection informations into actual suggestions. Defining
such a function is done in the languages folders (and this is where there code duplication).
-/

open Lean

/-! ## Data providers -/

section
open Elab

-- The next macro was written by Kyle Miller.
/-- Builds a data provider function. -/
macro "dataProvider " name:ident args:ident* " := " q:term : command => do
  let q ← q.replaceM fun s => do
    if s.isIdent && args.contains ⟨s⟩ then
      return Syntax.mkAntiquotNode `term s
    else
      return none
  let q' ← `(`($q))
  let args' := args.mapIdx fun i arg => (i, arg)
  let t := mkIdent `terms
  let body ← args'.foldrM (init := q') fun (i, arg) body => `(let $arg := $t[$(quote i)]; $body)
  `(def $name ($t : Array Term) : MetaM Term :=
    if h : ($t).size = $(quote args.size) then
      $body
    else
      failure)

dataProvider mkSelf a := a

dataProvider mkHalf a := a/2

dataProvider mkAddOne a := a + 1

dataProvider mkMin a b := min a b

dataProvider mkMax a b := max a b

dataProvider mkAdd a b := a + b

/-- Default data providers for numbers type, including adding one, taking the min, max and sum
of two numbers. -/
DataProviderList NumbersDefault := mkAddOne mkMin mkMax mkAdd

set_option hygiene false in
macro "useDefaultDataProviders" : command =>
`(configureDataProviders {
  ℝ : [mkSelf, mkHalf, NumbersDefault],
  ℕ : [mkSelf, NumbersDefault]})


open Meta

def SelectionInfo.mkBasicData (si : SelectionInfo) (typ : Expr) : MetaM (Array Expr) := do
  let typStr := toString (← ppExpr typ)
  let some decls := si.dataFVars[typStr] | return #[]
  let data ← decls.mapM (PrettyPrinter.delab ∘ LocalDecl.toExpr)
  let mut res : Array Expr := #[]
  let providers ← Verbose.getDataProviders
  for maker in providers.getD typ #[] do
    try
      res := res.push (← (Lean.Elab.Term.elabTerm (← maker data) typ).run')
    catch _ => continue
  return res

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

section
open Meta Server ProofWidgets

structure SuggestionsParams where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : Array SubExpr.GoalsLocation
  deriving RpcEncodable


open scoped Jsx Lean.SubExpr

def mkPanelRPC (mkCmdStr : (selectionInfo : SelectionInfo) → (goal : MVarId) → WidgetM Unit)
  (helpMsg : String) (title : String) (htmlId : String) (onlyGoal := false) (onlyOne := false) :
  (params : SuggestionsParams) → RequestM (RequestTask Html) :=
fun params ↦ RequestM.asTask do
let doc ← RequestM.readDoc
if h : 0 < params.goals.size then
  let goal := params.goals[0]
  let goalName := goal.mvarId.name
  let all := if onlyOne then "The selected sub-expression" else "All selected sub-expressions"
  let be_where := if onlyGoal then "in the main goal." else "in the main goal or its context."
  let errorMsg := s!"{all} should be {be_where}"
  let inner : Html ← (do
    if onlyOne && params.selectedLocations.size > 1 then
      return <span>{.text "You should select only one sub-expression"}</span>
    for selectedLocation in params.selectedLocations do
      if selectedLocation.mvarId.name != goalName then
        return <span>{.text errorMsg}</span>
      else if onlyGoal then
        if !(selectedLocation.loc matches (.target _)) then
          return <span>{.text errorMsg}</span>
    if params.selectedLocations.isEmpty then
      return <span>{.text helpMsg}</span>
    goal.ctx.val.runMetaM {} do
      let md ← goal.mvarId.getDecl
      let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx lctx md.localInstances do
        let selections ← mkSelectionInfos params.selectedLocations
        let curIndent := params.pos.character
        let (_, suggestions) ← (mkCmdStr selections[goal.mvarId].get! goal.mvarId).run default
        let mut children : Array Html := #[]
        for suggs in [suggestions.suggestionsPre, suggestions.suggestionsMain,
                      suggestions.suggestionsPost] do
          for ⟨linkText, newCode, range?⟩ in suggs do
            let props : MakeEditLinkProps := .ofReplaceRange doc.meta ⟨params.pos, params.pos⟩
                    (ppAndIndentNewLine curIndent newCode) range?
            children := children.push
              <li style={json% {"margin-bottom": "1rem"}}>
                <MakeEditLink edit={props.edit} newSelection?={props.newSelection?} title?={props.title?}>
                  {.text linkText}
                </MakeEditLink>
              </li>
        return .element "ul" #[("style", json% { "font-size": "125%"})] children)
  return <details «open»={true} id={htmlId}>
           <summary className="mv2 pointer">{.text title}</summary>
           <div className="ml1">{inner}</div>
         </details>
else
  return <span>{.text ""}</span> -- This shouldn't happen.

end

/-! ## Debugging instances -/

instance : Inhabited SubExpr.GoalLocation := ⟨.target SubExpr.Pos.root⟩

instance : ToString LocalDecl := ⟨toString ∘ LocalDecl.userName⟩

instance {α β : Type} [BEq α] [Hashable α] [ToString α] [ToString β] : ToString (Batteries.HashMap α β) :=
⟨fun MetaM ↦ "\n".intercalate <| MetaM.toList.map fun p : α × β ↦ s!"{p.1} : {p.2}"⟩

def debugMessage (msg : String) : WidgetM Unit := do
  if (← verboseConfigurationExt.get).debugSuggestionWidget then
    pushSuggestion msg

/-! ## Suggestion making -/

open Verbose Meta

def mkNewStuff (selectedForallME : VExpr) (selectedForallType : Expr) (data : Expr) (goal : MVarId)
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
      let hN ← goal.getUnusedUserName (.mkSimple <| "h"++ toString vN)
      withRenamedFVar v vN do
      let obtainedS ← PrettyPrinter.delab (propo.toExpr.instantiate1 data)
      pure [(vN, none), (hN, obtainedS)]
    | .exist_rel _e v _t rel rel_rhs propo => do
      let vN ← goal.getUnusedUserName v
      let relN : Name := .mkSimple s!"{v}{symb_to_hyp rel rel_rhs}"
      let relS ← mkRelStx vN rel rel_rhs
      let hN ← goal.getUnusedUserName (.mkSimple <| "h"++ toString vN)
      withRenamedFVar v vN do
      let obtainedS ← PrettyPrinter.delab (propo.toExpr.instantiate1 data)
      pure [(vN, none), (relN, some relS), (hN, obtainedS)]
    | _ => do
      let obtainedS ← PrettyPrinter.delab (obtained.instantiate1 data)
      pure [(newsIdent.getId, some obtainedS)]
  return (obtained, newS)

register_endpoint mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic)

register_endpoint mkShowTacStx (new : Term) : MetaM (TSyntax `tactic)

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


/-- Suggest to close the goal using the provided terms. Those terms should be proofs,
not statements.-/
register_endpoint mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic)

register_endpoint mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic)

def mkMaybeApp (selectedForallME : VExpr) (selectedForallIdent : Ident) (data : Expr) :
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

def mkMaybeAppStmt (selectedForallME : VExpr) (selectedForallStmt : Term) (data : Expr) :
    MetaM (List Term) := do
  match selectedForallME with
  | .forall_simple e _v _t prop => do
    match prop with
    | .impl ..=> do
      let leS ← PrettyPrinter.delab (e.bindingBody!.bindingDomain!.instantiate1 data)
      return [selectedForallStmt, leS]
    | _ => return [selectedForallStmt]
  | .forall_rel _ _ _ rel rhs _ => do
    let relS ← mkRelStx' data rel rhs
    return [selectedForallStmt, relS]
  | _ => unreachable!

/-- Suggest to close the goal using the provided terms. Those terms should be statements, not
proofs. -/
register_endpoint mkSinceConcludeTacStx (args : List Term) (goal : Term) : MetaM (TSyntax `tactic)

register_endpoint mkSinceObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic)

def makeSinceSuggestionsOnlyLocal (selectionInfo : SelectionInfo) (goal : MVarId) :
    WidgetM Unit := do
  if selectionInfo.onlyLocalDecls then do
  let forallFVars ← selectionInfo.forallFVars
  match forallFVars with
  | #[selectedForallDecl] => do
    let selectedForallType ← whnf selectedForallDecl.type
    -- We will try specializing the selected forall to each element of `datas`.
    let datas ← selectionInfo.mkData selectedForallType.bindingDomain!
    let newsIdent := mkIdent (← goal.getUnusedUserName `H)
    parse selectedForallType fun selectedForallME ↦ do
    for data in datas do
      let selectedForallStmt ← PrettyPrinter.delab selectedForallDecl.type
      let maybeAppTerms ← mkMaybeAppStmt selectedForallME selectedForallStmt data
      let (obtained, newStuff) ← mkNewStuff selectedForallME selectedForallType data goal newsIdent
      let goalType ← goal.getType
      let goalS ← PrettyPrinter.delab goalType
      let tac ← if ← isDefEq (obtained.instantiate1 data) goalType then
        mkSinceConcludeTacStx maybeAppTerms goalS
      else
        mkSinceObtainTacStx maybeAppTerms newStuff
      pushSuggestion (← toString <$> PrettyPrinter.ppTactic tac)
    if datas.isEmpty then
      debugMessage s!"Bouh typStr: {← liftM $ ppExpr selectedForallType.bindingDomain!}, si.dataFVars: {selectionInfo.dataFVars}, datas: {← liftM $ datas.mapM ppExpr}"
  | _ => debugMessage s!"Only local decls : {forallFVars.map (fun l ↦ l.userName)}"

register_endpoint mkUseTacStx (wit : Term) (newGoal : Option Term) : MetaM (TSyntax `tactic)

register_endpoint mkSinceTacStx (facts : Array Term) (concl : Term) : MetaM (TSyntax `tactic)

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

set_option hygiene false in
macro "useSinceSuggestionProviders" : command =>
`(configureSuggestionProviders mkUnfoldSuggestion
                               makeSuggestionsOnlyFullGoals
                               makeSuggestionsSingleProp
                               makeSuggestionsFullGoal
                               makeSinceSuggestionsOnlyLocal)
