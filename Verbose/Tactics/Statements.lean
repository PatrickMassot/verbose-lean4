import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod

import Mathlib.Tactic.Lemma
import Verbose.Infrastructure.Multilingual

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

register_endpoint mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic)

section victoryWidget
open Lean Server Elab Command
open ProofWidgets
open scoped Jsx

register_endpoint victoryMessage : CoreM String
register_endpoint noVictoryMessage : CoreM String

structure ProofStatusProps where
  message : String
  cssClasses : String
  deriving FromJson, ToJson

@[server_rpc_method]
def ProofStatus.rpc (props : ProofStatusProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    return <p className={props.cssClasses}>{.text props.message}</p>

@[widget_module]
def ProofStatus : Component ProofStatusProps :=
  mk_rpc_widget% ProofStatus.rpc

def ProofWidgets.savePanelWidgetInfo {α : Type} [RpcEncodable α]
    (c : Component α) (props : α) (stx : Syntax) : CoreM Unit :=
  Widget.savePanelWidgetInfo c.javascriptHash (rpcEncode props) stx

end victoryWidget

def mkExercise (name? : Option Ident) (objs hyps : TSyntaxArray ``bracketedBinder) (concl: Term)
    (prf?: Option (TSyntax ``tacticSeq)) (tkp tkq : Syntax) : CommandElabM Unit := do
  let ref := mkNullNode #[tkp, tkq]
  let prf ← prf?.getDM <| withRef ref `(tacticSeq| skip)
  let term ← withRef tkq `(by%$ref
    skip%$ref
    ($prf)
    skip%$ref)
  let config ← verboseConfigurationExt.get
  if config.useSuggestionWidget then
    let tac : TSyntax `tactic ← liftCoreM <| mkWidgetProof prf
    if let some name := name? then
      elabCommand (← `(command|lemma $name $(objs ++ hyps):bracketedBinder* : $concl := by {$tac}))
    else
      elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by {$tac}))
  else
    if let some name := name? then
      elabCommand (← `(command|lemma $name $(objs ++ hyps):bracketedBinder* : $concl := $term))
    else
      elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := $term))
  if let some name := name? then
    if config.autoRegisterAnonymousLemma then
      elabCommand (← `(command|addAnonymousFactSplittingLemma $name))
  let x := (← get).messages.forM (m := StateT Bool IO) fun m => do
    let s ← m.data.toString
    if m.severity == .error || s.endsWith "declaration uses 'sorry'" || s.startsWith "unsolved goals" then
      set false
  let (_, isDone) ← x.run true
  let message : String ← liftCoreM <| if isDone then victoryMessage else noVictoryMessage
  let cssClasses := if isDone then "f2 gold" else ""
  liftCoreM <| ProofWidgets.savePanelWidgetInfo ProofStatus { message, cssClasses } tkq
