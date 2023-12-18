import Verbose.Tactics.Help


def Std.HashMap.insertOrModify {α : Type*} {_ : BEq α} {_ : Hashable α} {β : Type*} (self : Std.HashMap α β)
  (a : α) (f : α → β → β) (b : β): Std.HashMap α β :=
if self.contains a then
  self.modify a f
else
  self.insert a b

open Lean Meta Server

open ProofWidgets

section

structure SelectionInfo where
  /-- Whether the full goal is selected. -/
  fullGoal : Bool := false
  /-- Subexpressions selected in the goal.
  Not including the root subexpression whose presence is recorded in the `fullGoal` field. -/
  goalSubExprs : Array SubExpr.Pos := ∅
  /-- Selected data-carrying free variables. The key is a string representating the type. -/
  dataFVars : Std.HashMap String (Array LocalDecl) := ∅
  /-- Selected data-carrying free variables. The key is a string representating the type.
  A free variable is considered selected if either its name or its full type is selected. -/
  propFVars : Array LocalDecl := ∅
  fVarsTypeSubExprs : Std.HashMap FVarId (LocalDecl × Array SubExpr.Pos) := ∅
  fVarsValueSubExprs : Std.HashMap FVarId (LocalDecl × Array SubExpr.Pos) := ∅
  deriving Inhabited

def SelectionInfo.onlyGoal (si : SelectionInfo) : Bool :=
  si.dataFVars.isEmpty && si.propFVars.isEmpty && si.fVarsTypeSubExprs.isEmpty && si.fVarsValueSubExprs.isEmpty

def SelectionInfo.onlyFullGoal (si : SelectionInfo) : Bool := si.onlyGoal && si.fullGoal

def SelectionInfo.singleData (si : SelectionInfo) : Option LocalDecl :=
  if !si.fullGoal && si.goalSubExprs.isEmpty && si.propFVars.isEmpty && si.fVarsTypeSubExprs.isEmpty && si.fVarsValueSubExprs.isEmpty && si.dataFVars.size = 1 then
    some si.dataFVars.toList[0]!.2[0]!
  else
    none

def SelectionInfo.singleProp (si : SelectionInfo) : Option LocalDecl :=
  if !si.fullGoal && si.goalSubExprs.isEmpty && si.dataFVars.isEmpty && si.fVarsTypeSubExprs.isEmpty && si.fVarsValueSubExprs.isEmpty && si.propFVars.size = 1 then
    some si.propFVars[0]!
  else
    none

elab "foo" x:term : tactic => do
  let e ← Elab.Tactic.elabTerm x none
  dbg_trace e

example (x : ℝ) : True := by
 foo x/2

#check OfNat.ofNat

def SelectionInfo.mkData (si : SelectionInfo) (typ : String) : MetaM (Array Expr) := do
  let some decls := si.dataFVars[typ] | return #[]
  if decls.size = 1 then
    let base := decls[0]!.toExpr
    let half ← mkAppM `HDiv.hDiv #[base, (←mkAppM `OfNat.ofNat #[Expr.lit (Literal.natVal 2)])]
    return #[base, half]
  return #[]



abbrev SelectionInfos := Std.HashMap MVarId SelectionInfo

def mkSelectionInfos (selected : Array SubExpr.GoalsLocation) : MetaM SelectionInfos := do
  let mut res : SelectionInfos := ∅
  for ⟨goal, loc⟩ in selected do
    res ← goal.withContext do
      let ctx ← getLCtx
      match loc with
      | .hyp fvar => do
        let ld := ctx.get! fvar
        pushFVar ld res goal
      | .target pos =>
        if pos.isRoot then
          pure <| res.insertOrModify goal
            (fun _ info ↦ {info with fullGoal := true}) {fullGoal := true}
        else
          pure <| res.insertOrModify goal
            (fun _ info ↦ {info with goalSubExprs := info.goalSubExprs.push pos})
            {goalSubExprs := #[pos]}
      | .hypValue fvar pos =>
         let ld := ctx.get! fvar
         if pos.isRoot then
           pushFVar ld res goal
         else
           pure <| res.insertOrModify goal
            (fun _ info ↦ {info with
              fVarsValueSubExprs := info.fVarsValueSubExprs.insertOrModify fvar
                                      (fun _ ⟨ld, epos⟩ ↦ (ld, epos.push pos)) (ld, #[pos])})
            {fVarsValueSubExprs := Std.HashMap.empty.insert fvar (ld, #[pos])}
      | .hypType fvar pos =>
         let ld := ctx.get! fvar
         if pos.isRoot then
           pushFVar ld res goal
         else
           pure <| res.insertOrModify goal
             (fun _ info ↦ {info with
               fVarsTypeSubExprs := info.fVarsTypeSubExprs.insertOrModify fvar
                                      (fun _ ⟨ld, epos⟩ ↦ (ld, epos.push pos)) (ld, #[pos])})
             {fVarsTypeSubExprs := Std.HashMap.empty.insert fvar (ld, #[pos])}
  return res

  where pushFVar (ld : LocalDecl) (res : SelectionInfos) (goal : MVarId) := do
    if (← instantiateMVars (← inferType ld.type)).isProp then
      pure <| res.insertOrModify goal
        (fun _ info ↦ {info with propFVars := info.propFVars.push ld}) {propFVars := #[ld]}
    else
      let typStr := toString (← ppExpr ld.type)
      pure <| res.insertOrModify goal
        (fun _ info ↦ {info with
         dataFVars := info.dataFVars.insertOrModify typStr
          (fun _ a ↦ a.push ld) #[ld]})
        {dataFVars := Std.HashMap.empty.insert typStr #[ld]}

end

structure SuggestionsParams where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : Array SubExpr.GoalsLocation
  deriving RpcEncodable

structure SuggestionInfo where
  linkText : String
  insertedText : String
  /-- The part of the inserted text that will be selected after insertion. -/
  selected : Option (String.Pos × String.Pos) := none

open scoped Jsx in open Lean.SubExpr in
def mkPanelRPC
    (mkCmdStr : (selectionInfo : SelectionInfo) → (goal : MVarId) → SuggestionsParams →
   MetaM (Array SuggestionInfo))
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
        let suggestions ← mkCmdStr selections[mainGoal.mvarId].get! mainGoal.mvarId
          params
        let mut children : Array Html := #[]
        for ⟨linkText, newCode, range?⟩ in suggestions do
          children := children.push <| .ofComponent
            MakeEditLink
            (.ofReplaceRange doc.meta ⟨params.pos, params.pos⟩ newCode range?)
            #[ .text linkText ]
        return Html.element "div" #[] children)
  return <details «open»={true}>
      <summary className="mv2 pointer">{.text title}</summary>
      <div className="ml1">{inner}</div>
    </details>
else
  return <span>{.text "There is no goal to solve!"}</span> -- This shouldn't happen.

def Lean.SubExpr.GoalLocation.isGoalRoot : Lean.SubExpr.GoalLocation → Bool
| target pos => pos.isRoot
| _ => false

instance : Inhabited SubExpr.GoalLocation := ⟨.target SubExpr.Pos.root⟩

open Verbose
def makeSuggestions (selectionInfo : SelectionInfo) (goal : MVarId)
    (params : SuggestionsParams) : MetaM (Array SuggestionInfo) :=
  withoutModifyingState do
  if selectionInfo.onlyFullGoal then
    let (s, _msg) ← gatherSuggestions (helpAtGoal goal)
      return ← s.mapM fun sug ↦ do
        let text ← sug.suggestion.pretty
        pure ⟨toString text, toString text, none⟩
  if let some ld := selectionInfo.singleProp then
    let (s, _msg) ← gatherSuggestions (helpAtHyp goal ld.userName)
      return ← s.mapM fun sug ↦ do
        let text ← sug.suggestion.pretty
        pure ⟨toString text, toString text, none⟩
  if selectionInfo.fullGoal then
    parse (← goal.getType) fun goalME ↦ do
    match goalME with
    | .exist_simple _e var typ prop => do
      let typStr := toString (← ppExpr typ)
      let wits ← selectionInfo.mkData typStr
      let mut sugs := #[]
      for wit in wits do
        let witS ← PrettyPrinter.delab wit
          -- **FIXME** this FVar renaming approach won't work for more general witnesses such
          -- as `ε/2` or `max N₁ N₂`.
        sugs := sugs.push (← do
        let newGoal ← prop.delab
        let tac ← `(tactic|Montrons que $witS convient : $newGoal)
        toString <$> (PrettyPrinter.ppTactic tac))
      return sugs.map fun x ↦ ⟨x, x, none⟩
      /- if let some decls := selectionInfo.dataFVars[typStr] then
        let mut sugs := #[]
        for decl in decls do
          let witS ← PrettyPrinter.delab decl.toExpr
          -- **FIXME** this FVar renaming approach won't work for more general witnesses such
          -- as `ε/2` or `max N₁ N₂`.
          sugs := sugs.push (← withRenamedFVar var decl.userName do
          let newGoal ← prop.delab
          let tac ← `(tactic|Montrons que $witS convient : $newGoal)
          toString <$> (PrettyPrinter.ppTactic tac))

        return sugs.map fun x ↦ ⟨x, x, none⟩
      else
        return #[⟨",".intercalate selectionInfo.dataFVars.keys, "exist_simple", none ⟩] -/
    | _ => do return #[]
  else
    return #[]
  /- let locs := params.selectedLocations.map SubExpr.GoalsLocation.loc
  let ctx ← getLCtx
  if locs.size = 1 then
    let loc := locs[0]!
    if loc.isGoalRoot then
      let (s, _msg) ← gatherSuggestions (helpAtGoal goal)
      return ← s.mapM fun sug ↦ do
        let text ← sug.suggestion.pretty
        pure ⟨toString text, toString text, none⟩
    else if let .hyp fvar := loc then
      let (s, _msg) ← gatherSuggestions (helpAtHyp goal (← fvar.getUserName))
      return ← s.mapM fun sug ↦ do
        let text ← sug.suggestion.pretty
        pure ⟨toString text, toString text, none⟩
    -- TODO: If there is only one selection and it is in a `hypType` and corresponds to a const
    -- or const application then propose to unfold definition
  let mut selectedFVarsTypes : Array (Name × Expr × Expr) := #[]
  for loc in locs do
    if let .hyp fvar := loc then
      let ld := ctx.get! fvar
      selectedFVarsTypes := selectedFVarsTypes.push (ld.userName, ld.toExpr, ld.type)
  parse (← goal.getType) fun goalME ↦ do
  match goalME with
  | .exist_simple _e var typ prop => do
    let relevantFVarsTypes ← selectedFVarsTypes.filterM (fun x ↦ isDefEq typ x.2.2)
    if relevantFVarsTypes.size = 1 then
      let witS ← PrettyPrinter.delab relevantFVarsTypes[0]!.2.1
      -- **FIXME** this FVar renaming approach won't work for more general witnesses such
      -- as `ε/2` or `max N₁ N₂`.
      withRenamedFVar var relevantFVarsTypes[0]!.1 do
      let newGoal ← prop.delab
      let tac ← `(tactic|Montrons que $witS convient : $newGoal)
      let sugg ← PrettyPrinter.ppTactic tac
      return #[⟨toString sugg, toString sugg, none⟩]
    else
      return #[⟨s!"Yo {selectedFVarsTypes}", "", none⟩]
  | _ => do return #[⟨"No idea", "", none⟩] -/
  /- let mut res  := ""
  for loc in locs do
    match loc with
    | .hyp fvar => do
      let ld := ctx.get! fvar
      res := s!"{res}{ld.userName}"
    | .target pos =>
      res := if pos.isRoot then
               s!"{res} Goal root"
             else
               res
    | .hypValue fvar pos => pure ()
    | .hypType fvar pos => pure () -/


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
    savePanelWidgetInfo stx `suggestionsPanel (pure .null)
    Lean.Elab.Tactic.evalTacticSeq seq
  | _ => Lean.Elab.throwUnsupportedSyntax


example (n : Nat) (h : ∀ l : Nat, l = l) : ∃ k : Nat, k = k := by
 with_suggestions

 refine ⟨0, ?_⟩
 trivial
