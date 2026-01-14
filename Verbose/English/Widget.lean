import Verbose.Tactics.Widget
import Verbose.English.Help

namespace Verbose.English
open Lean Meta Server

open ProofWidgets

implement_endpoint (lang := en) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|We reformulate $hyp as $new)

implement_endpoint (lang := en) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Let's prove that $new)

implement_endpoint (lang := en) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeApplied args
`(tactic|We conclude by $concl)

implement_endpoint (lang := en) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeApplied args
let newStuff ← listMaybeTypedIdentToNewStuffSuchThatEN news
`(tactic|By $maybeApp we get $newStuff)

implement_endpoint (lang := en) mkSinceConcludeTacStx (args : List Term) (goalS : Term) : MetaM (TSyntax `tactic) := do
let concl ← arrayToFacts args.toArray
`(tactic|Since $concl we conclude that $goalS)

-- FIXME: the code below is probably too specific. Need something more principled
implement_endpoint (lang := en) mkSinceObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
    MetaM (TSyntax `tactic) := do
  let facts ← arrayToFacts args.toArray
  match news with
  | [(_, some stmt)] =>
      `(tactic|Since $facts we get that $stmt:term)
  | _ =>
      let newStuff ← listMaybeTypedIdentToNewObjectNameLess news
      `(tactic|Since $facts we get $newStuff:newObjectNameLess)

implement_endpoint (lang := en) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Let's prove that $wit works : $goal)
| none => `(tactic|Let's prove that $wit works)

implement_endpoint (lang := en) mkSinceTacStx (facts : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsS ← arrayToFacts facts
  `(tactic|Since $factsS we conclude that $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Use shift-click to select sub-expressions."
  "Suggestions"
  "suggestions"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions, incremental]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx => do
    Elab.Term.withNarrowedArgTacticReuse 1 Lean.Elab.Tactic.evalTacticSeq stx
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx
