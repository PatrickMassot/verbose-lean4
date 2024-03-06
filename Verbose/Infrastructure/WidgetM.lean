import Lean
import Mathlib.Data.String.Defs

open Lean

structure SuggestionInfo where
  linkText : String
  insertedText : String
  /-- The part of the inserted text that will be selected after insertion. -/
  selected : Option (String.Pos × String.Pos) := none
  deriving BEq

inductive SuggestionKind | Pre | Main | Post

structure Verbose.WidgetState where
  suggestionsPre : Array SuggestionInfo
  suggestionsMain : Array SuggestionInfo
  suggestionsPost : Array SuggestionInfo
  deriving Inhabited

abbrev WidgetM := StateRefT Verbose.WidgetState MetaM

instance : Lean.MonadBacktrack Lean.Meta.SavedState WidgetM :=
⟨saveState (m := MetaM), fun s ↦ restoreState (m := MetaM) s⟩

def pushSuggestionKind (kind : SuggestionKind) (linkText : String)
    (insertedText : Option String := none) (selected : Option (String.Pos × String.Pos) := none) :
    WidgetM Unit := do
  let insertedText := insertedText.getD linkText
  let new : SuggestionInfo := ⟨linkText, insertedText, selected⟩
  let cur ← get
  if cur.suggestionsPre.contains new || cur.suggestionsMain.contains new ||
      cur.suggestionsPost.contains new then
    return
  match kind with
  | .Pre  => set {cur with suggestionsPre := cur.suggestionsPre.push new }
  | .Main => set {cur with suggestionsMain := cur.suggestionsMain.push new }
  | .Post => set {cur with suggestionsPost := cur.suggestionsPost.push new }

def pushPreSuggestion (linkText : String)
    (insertedText : Option String := none) (selected : Option (String.Pos × String.Pos) := none) :
    WidgetM Unit := pushSuggestionKind .Pre linkText insertedText selected

def pushSuggestion (linkText : String)
    (insertedText : Option String := none) (selected : Option (String.Pos × String.Pos) := none) :
    WidgetM Unit := pushSuggestionKind .Main linkText insertedText selected

def pushPostSuggestion (linkText : String)
    (insertedText : Option String := none) (selected : Option (String.Pos × String.Pos) := none) :
    WidgetM Unit := pushSuggestionKind .Post linkText insertedText selected

def debugMessage (msg : String) : WidgetM Unit := do
  if (← getOptions).getBool `verbose.suggestion_debug then
    pushSuggestion msg

def ppAndIndentNewLine (indent : Nat) (text : Format) :=
toString (Format.nest indent text) ++ "\n" ++ (String.replicate indent ' ')
