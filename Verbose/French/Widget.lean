import Verbose.Tactics.Widget
import Verbose.French.Help

namespace Verbose.French
open Lean Meta Server

open ProofWidgets

endpoint (lang := fr) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|On reformule $hyp en $new)

endpoint (lang := fr) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Montrons que $new)

endpoint (lang := fr) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeApplied args
`(tactic|On conclut par $concl)

endpoint (lang := fr) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeApplied args
let newStuff ← listMaybeTypedIdentToNewStuffSuchThatFR news
`(tactic|Par $maybeApp on obtient $newStuff)

endpoint (lang := fr) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Montrons que $wit convient : $goal)
| none => `(tactic|Montrons que $wit convient)

endpoint (lang := fr) mkSinceTacStx (facts : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsS ← arrayToFactsFR facts
  `(tactic|Comme $factsS on conclut que $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Utilisez shift-clic pour sélectionner des sous-expressions."
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
