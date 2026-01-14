import Verbose.Tactics.Widget
import Verbose.French.Help

namespace Verbose.French
open Lean Meta Server

open ProofWidgets

implement_endpoint (lang := fr) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|On reformule l'hypothèse $hyp en $new)

implement_endpoint (lang := fr) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Montrons que $new)

implement_endpoint (lang := fr) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeApplied args
`(tactic|On conclut par $concl)

implement_endpoint (lang := fr) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeApplied args
let newStuff ← listMaybeTypedIdentToNewStuffSuchThatFR news
`(tactic|Par $maybeApp on obtient $newStuff)

implement_endpoint (lang := fr) mkSinceConcludeTacStx (args : List Term) (goalS : Term) : MetaM (TSyntax `tactic) := do
let concl ← arrayToFactsFR args.toArray
`(tactic|Comme $concl on conclut que $goalS)

-- FIXME: the code below is probably too specific. Need something more principled
-- Also it probably fails when there are two existential (see the commit adding this comment)
implement_endpoint (lang := fr) mkSinceObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
    MetaM (TSyntax `tactic) := do
  let facts ← arrayToFactsFR args.toArray
  match news with
  | [(_, some stmt)] =>
      `(tactic|Comme $facts on obtient que $stmt:term)
  | _ =>
      let newStuff ← listMaybeTypedIdentToNewObjectFR news
      `(tactic|Comme $facts on obtient $newStuff:newObjectFR)

implement_endpoint (lang := fr) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Montrons que $wit convient : $goal)
| none => `(tactic|Montrons que $wit convient)

implement_endpoint (lang := fr) mkSinceTacStx (facts : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsS ← arrayToFactsFR facts
  `(tactic|Comme $factsS on conclut que $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Utilisez shift-clic pour sélectionner des sous-expressions."
  "Suggestions" "suggestions"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions, incremental]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx => do
    Elab.Term.withNarrowedArgTacticReuse 1 Lean.Elab.Tactic.evalTacticSeq stx
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx
