import Verbose.Tactics.Help

open Lean Meta Server

open ProofWidgets

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
    (mkCmdStr : (pos : Array GoalsLocation) → (goal : MVarId) → SuggestionsParams →
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
        let suggestions ← mkCmdStr params.selectedLocations mainGoal.mvarId
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

def makeSuggestions (_pos : Array Lean.SubExpr.GoalsLocation) (goal : MVarId)
    (params : SuggestionsParams) : MetaM (Array SuggestionInfo) := do
  let locs := params.selectedLocations.map SubExpr.GoalsLocation.loc
  let ctx ← getLCtx
  if locs.size = 1 then
    if locs[0]!.isGoalRoot then
      let (s, _msg) ← Verbose.gatherSuggestions (Verbose.helpAtGoal goal)
      return ← s.mapM fun sug ↦ do
        let text ← sug.suggestion.pretty
        pure ⟨toString text, "Test", none⟩
    else if let .hyp fvar := locs[0]! then
      let (s, _msg) ← Verbose.gatherSuggestions (Verbose.helpAtHyp goal (← fvar.getUserName))
      return ← s.mapM fun sug ↦ do
        let text ← sug.suggestion.pretty
        pure ⟨toString text, "Test", none⟩
  let mut res  := ""
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
    | .hypType fvar pos => pure ()
  return #[⟨"Yo " ++ res, "Test", none⟩]

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


example (n : Nat) (h : ∀ l : Nat, l = l) : ∃ k : Nat, True := by
 with_suggestions

 refine ⟨0, ?_⟩
 trivial
