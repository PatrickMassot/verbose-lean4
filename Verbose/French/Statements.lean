import Verbose.Tactics.Statements
import Verbose.French.Widget

import ProofWidgets.Demos.Macro
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)
open Lean Server Elab Command
open ProofWidgets
open scoped Jsx

structure ProofStatusProps where
  isDone : Bool
  deriving FromJson, ToJson

@[server_rpc_method]
def ProofStatus.rpc (props : ProofStatusProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    if props.isDone then
        return <p className="f2 gold">Gagné 🎉</p>
      else
        return <p>Il faut travailler plus.</p>

@[widget_module]
def ProofStatus : Component ProofStatusProps :=
  mk_rpc_widget% ProofStatus.rpc

def ProofWidgets.savePanelWidgetInfo {α : Type} [RpcEncodable α]
    (c : Component α) (props : α) (stx : Syntax) : CoreM Unit :=
  Widget.savePanelWidgetInfo c.javascriptHash (rpcEncode props) stx


implement_endpoint (lang := fr) mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

/- **TODO**  Allow omitting Données or Hypothèses. -/

elab ("Exercice"<|>"Exemple") str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    tkp:"Démonstration :" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise none objs hyps concl prf? tkp tkq
  let x := (← get).messages.forM (m := StateT Bool IO) fun m => do
    let s ← m.data.toString
    if m.severity == .error || s.endsWith "declaration uses 'sorry'" || s.startsWith "unsolved goals" then
      set false
  let (_, isDone) ← x.run true
  liftCoreM <| ProofWidgets.savePanelWidgetInfo ProofStatus { isDone } tkq

elab ("Exercice-lemme"<|>"Lemme") name:ident str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    tkp:"Démonstration :" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
