import Verbose.Tactics.Widget
import Verbose.Spanish.Help

namespace Verbose.Spanish
open Lean Meta Server

open ProofWidgets

implement_endpoint (lang := es) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Reformulamos $hyp como $new)

implement_endpoint (lang := es) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Probemos que $new)

implement_endpoint (lang := es) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeApplied args
`(tactic|Concluimos por $concl)

implement_endpoint (lang := es) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeApplied args
let newStuff ← listMaybeTypedIdentToNewStuffSuchThatES news
`(tactic|Por $maybeApp tenemos $newStuff)

implement_endpoint (lang := es) mkSinceConcludeTacStx (args : List Term) (goalS : Term) : MetaM (TSyntax `tactic) := do
let concl ← arrayToFactsES args.toArray
`(tactic|Como $concl concluimos que $goalS)

-- FIXME: the code below is probably too specific. Need something more principled
implement_endpoint (lang := es) mkSinceObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
    MetaM (TSyntax `tactic) := do
  let facts ← arrayToFactsES args.toArray
  match news with
  | [(_, some stmt)] =>
      `(tactic|Como $facts tenemos que $stmt:term)
  | _ =>
      let newStuff ← listMaybeTypedIdentToNewObjectNameLessES news
      `(tactic|Como $facts se tiene $newStuff:newObjectNameLessES)

implement_endpoint (lang := es) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Probemos que $wit basta : $goal)
| none => `(tactic|Probemos que $wit basta)

implement_endpoint (lang := es) mkSinceTacStx (facts : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsS ← arrayToFactsES facts
  `(tactic|Como $factsS concluimos que $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Utiliza shift+clic para seleccionar subexpresiones"
  "Sugerencias"
  "sugerencias"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions, incremental]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx => do
    Elab.Term.withNarrowedArgTacticReuse 1 Lean.Elab.Tactic.evalTacticSeq stx
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx
