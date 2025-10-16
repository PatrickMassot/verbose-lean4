import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod

import Mathlib.Tactic.Lemma
import Verbose.Infrastructure.Multilingual
import Verbose.Tactics.Common

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

register_endpoint mkWidgetProof (prf : TSyntax ``tacticSeq) (tkp : Syntax) : CoreM (TSyntax `tactic)

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

open Language in
/--
Simple snapshot that remembers the previous expansion so we can compare it against the new one
for reuse.
-/
structure SimpleMacroExpandedSnapshot extends Language.Snapshot where
  newStx : Syntax
  next   : SnapshotTask DynamicSnapshot
deriving TypeName

open Language in
instance : ToSnapshotTree SimpleMacroExpandedSnapshot where
  toSnapshotTree s := ⟨s.toSnapshot, #[s.next.map (sync := true) toSnapshotTree]⟩

syntax (name := withoutSuggestions) "without_suggestions" tacticSeq : tactic

@[tactic withoutSuggestions, incremental]
def withoutPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx => do
    Elab.Term.withNarrowedArgTacticReuse 1 Lean.Elab.Tactic.evalTacticSeq stx

def mkExercise (name? : Option Ident) (objs hyps : TSyntaxArray ``bracketedBinder) (concl: Term)
    (prf?: Option (TSyntax ``tacticSeq)) (tkp tkq : Syntax) : CommandElabM Unit := do
  let ref := mkNullNode #[tkp, tkq]
  let prf ← prf?.getDM <| withRef ref `(tacticSeq| skip)
  let config ← verboseConfigurationExt.get
  -- show unsolved goals on `QED`
  let done ← withRef tkq `(tactic| done)
  -- make sure to use `tkp` as the ref for everything in front of `prf` so incrementality is not
  -- disabled early
  let term ← if config.useSuggestionWidget then
    let tac : TSyntax `tactic ← liftCoreM <| mkWidgetProof prf tkp
    withRef tkp `(by $tac:tactic; $done)
  else
    let tac ← Lean.TSyntax.mkInfoCanonical <$> `(tactic| without_suggestions%$tkp $prf)
    withRef tkp `(by $tac:tactic; $done)
  let stx ← if let some name := name? then
    `(command|lemma $name $(objs ++ hyps):bracketedBinder* : $concl := $term)
  else
    withRef tkp `(command|example $(objs ++ hyps):bracketedBinder* : $concl := $term)
  if let some snap := (←read).snap? then  -- incrementality enabled?
    let prom ← IO.Promise.new
    -- Store expansion for future reuse
    snap.new.resolve <| .ofTyped {
      diagnostics := .empty
      newStx := stx
      next := { stx? := none, task := prom.resultD default }
      : SimpleMacroExpandedSnapshot
    }
    -- Restore previous expansion so `example`'s incrementality can do its magic
    withReader ({ · with snap? := some {
      new := prom
      old? := do
        let oldSnap ← snap.old?
        let old ← oldSnap.val.get.toTyped? SimpleMacroExpandedSnapshot
        return { stx := old.newStx, val := old.next }
    } }) do
      elabCommand stx
      -- just to be sure, obsolete in next Lean release
      prom.resolve default
  else
    elabCommand stx
  -- Just to be sure, disable incrementality in the remainder
  withoutCommandIncrementality true do
    if let some name := name? then
      if config.autoRegisterAnonymousLemma then
        elabCommand (← `(command|addAnonymousFactSplittingLemma $name))
    let x := (← get).messages.reportedPlusUnreported.forM (m := StateT Bool IO) fun m => do
      let s ← m.data.toString
      if m.severity == .error || s.endsWith "declaration uses 'sorry'" || s.startsWith "unsolved goals" then
        set false
    let (_, isDone) ← x.run true
    let message : String ← liftCoreM <| if isDone then victoryMessage else noVictoryMessage
    let cssClasses := if isDone then "f2 gold" else ""
    liftCoreM <| ProofWidgets.savePanelWidgetInfo ProofStatus { message, cssClasses } tkq
