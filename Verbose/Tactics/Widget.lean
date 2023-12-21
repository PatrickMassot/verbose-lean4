import Verbose.Tactics.Initialize
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

def SelectionInfo.onlyLocalDecls (si : SelectionInfo) : Bool :=
  !si.fullGoal && si.goalSubExprs.isEmpty

def SelectionInfo.forallFVars (si : SelectionInfo) : MetaM (Array LocalDecl) :=
  si.propFVars.filterM (fun fvar ↦ do return (←whnf fvar.type) matches .forallE ..)

def Lean.Expr.isExists (e : Expr) : Bool :=
  e.getAppFn' matches .const `Exists _

def SelectionInfo.simplePropFVars (si : SelectionInfo) : MetaM (Array LocalDecl) :=
  si.propFVars.filterM (fun fvar ↦ do let typ ← whnf fvar.type; return (!typ matches .forallE .. && !typ.isExists))


/- elab "foo" x:term : tactic => do
  let e ← Elab.Tactic.elabTerm x none
  dbg_trace e -/

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
    (mkCmdStr : (selectionInfo : SelectionInfo) → (goal : MVarId) → (selected : Array GoalsLocation) → MetaM (Array SuggestionInfo))
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
        let suggestions ← mkCmdStr selections[mainGoal.mvarId].get! mainGoal.mvarId params.selectedLocations
        let mut children : Array Html := #[]
        for ⟨linkText, newCode, range?⟩ in suggestions do
          children := children.push <| Html.element "li" #[("style", json% {"margin-bottom": "1rem"})] #[.ofComponent
            MakeEditLink
            (.ofReplaceRange doc.meta ⟨params.pos, params.pos⟩ newCode range?)
            #[ .text linkText ]]


        return Html.element "ul" #[("style", json% { "font-size": "150%"})] children)
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

instance : ToString LocalDecl := ⟨toString ∘ LocalDecl.userName⟩

instance {α β : Type} [BEq α] [Hashable α] [ToString α] [ToString β] : ToString (Std.HashMap α β) :=
⟨fun m ↦ "\n".intercalate <| m.toList.map fun p : α × β ↦ s!"{p.1} : {p.2}"⟩

open Verbose

def mkMaybeApp (selectedForallME : MyExpr) (selectedForallIdent : Ident) (data : Expr) :
    MetaM (TSyntax `maybeAppliedFR) := do
  let dataS ← PrettyPrinter.delab data
  match selectedForallME with
  | .forall_simple e _v _t prop => do
    match prop with
    | .impl ..=> do
      let leS ← PrettyPrinter.delab (e.bindingBody!.bindingDomain!.instantiate1 data)
      `(maybeAppliedFR|$selectedForallIdent:term appliqué à $dataS:term en utilisant que $leS)
    | _ => `(maybeAppliedFR|$selectedForallIdent:term appliqué à $dataS:term)
  | .forall_rel _ _ _ rel rhs _ => do
    let relS ← mkRelStx' data rel rhs
    `(maybeAppliedFR|$selectedForallIdent:term appliqué à $dataS:term en utilisant que $relS)
  | _ => unreachable!

def mkNewStuff (selectedForallME : MyExpr) (selectedForallType : Expr) (data : Expr) (goal : MVarId)
    (newsIdent : Ident) : MetaM (Expr × TSyntax `newStuffFR) := do
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
      `(newStuffFR|$vS:ident tel que $hS:ident : $obtainedS:term)
    | .exist_rel _e v _t rel rel_rhs propo => do
      let vN ← goal.getUnusedUserName v
      let vS := mkIdent vN
      let relI := mkIdent s!"{v}{symb_to_hyp rel rel_rhs}"
      let relS ← mkRelStx vN rel rel_rhs
      let hS := mkIdent (← goal.getUnusedUserName ("h"++ toString vN : String))
      withRenamedFVar v vN do
      let obtainedS ← PrettyPrinter.delab (propo.toExpr.instantiate1 data)
      `(newStuffFR|$vS:ident tel que ($relI : $relS) ($hS:ident : $obtainedS:term))
    | _ => do
      let obtainedS ← PrettyPrinter.delab (obtained.instantiate1 data)
      `(newStuffFR|$newsIdent:ident : $obtainedS:term)
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
      if let some e ← ld.type.expandHeadFun then
        let hI := mkIdent ld.userName
        let eS ← PrettyPrinter.delab e
        let s ← toString <$> PrettyPrinter.ppTactic (← `(tactic| On reformule $hI en $eS))
        return #[⟨s, s ++ "\n  ", none⟩]
      else
        return if debug then #[⟨"Could not expand", "", none⟩] else #[]
    | .hypType fvarId pos => do
      let ld := ctx.get! fvarId
      try
        let expanded ← replaceSubexpr Lean.Expr.expandHeadFun! pos ld.type
        let hI := mkIdent ld.userName
        let eS ← PrettyPrinter.delab expanded
        let s ← toString <$> PrettyPrinter.ppTactic (← `(tactic| On reformule $hI en $eS))
        return #[⟨s, s ++ "\n  ", none⟩]
      catch _ => return if debug then #[⟨"Could not expand", "", none⟩] else #[]
    | .hypValue .. => return if debug then #[⟨"Cannot expand def in a value", "", none⟩] else #[]
    | .target pos => do
      try
        let expanded ← replaceSubexpr Lean.Expr.expandHeadFun! pos (← goal.getType)
        let eS ← PrettyPrinter.delab expanded
        let s ← toString <$> PrettyPrinter.ppTactic (←  `(tactic| Montrons que $eS))
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

      let (obtained, newStuff) ← mkNewStuff selectedForallME selectedForallType data goal newsIdent
      let tac ← if ← isDefEq (obtained.instantiate1 data) (← goal.getType) then
        `(tactic|On conclut par $maybeApp:maybeAppliedFR)
      else
        `(tactic|Par $maybeApp:maybeAppliedFR on obtient $newStuff)
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
        let tac ← `(tactic|Montrons que $witS convient : $newGoal)
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
    savePanelWidgetInfo stx `suggestionsPanel (pure .null)
    Lean.Elab.Tactic.evalTacticSeq seq
  | _ => Lean.Elab.throwUnsupportedSyntax


example (n m : Nat) (h : ∀ l : Nat, l = l) : ∃ k : Nat, k = k := by
 with_suggestions

 refine ⟨0, ?_⟩
 trivial

example (n m : Nat) (hn : 2 ≤ n) (h : ∀ l ≥ 2, l = l) : ∃ k ≥ 3, k = k := by
 with_suggestions

 refine ⟨3, ?_⟩
 trivial


namespace TEST
def continue_en (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def tend_vers (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

open Lean Elab Meta  Tactic in
elab "showE" x:term : tactic => withMainContext do
  let e ← Elab.Tactic.elabTerm x none
  logInfo s!"{e}\n"

open Lean Elab Meta  Tactic in
elab "typeE" x:term : tactic => withMainContext do
  let e ← Elab.Tactic.elabTerm x none
  let t ← inferType e
  logInfo s!"{t}\n"

-- set_option verbose.suggestion_debug true in
example (x₀ : ℝ) (f : ℝ → ℝ) (hf : continue_en f x₀) (u : ℕ → ℝ) (hu : tend_vers u x₀) :
    tend_vers (f ∘ u) (f x₀) := by
  with_suggestions
  Montrons que ∀ ε > 0, ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε
  Soit ε > 0
  Par hf appliqué à ε en utilisant que ε > 0 on obtient
    δ tel que (δ_pos : δ > 0) (hδ : ∀ (x : ℝ), |x - x₀| ≤ δ → |f x - f x₀| ≤ ε)
  Par hu appliqué à δ en utilisant que δ > 0 on obtient N tel que hN : ∀ n ≥ N, |u n - x₀| ≤ δ
  Montrons que N convient : ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε
  Soit n ≥ N
  Par hN appliqué à n en utilisant que n ≥ N on obtient H : |u n - x₀| ≤ δ
  On conclut par hδ appliqué à u n en utilisant que |u n - x₀| ≤ δ
