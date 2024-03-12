import Verbose.Tactics.Common

open Lean

namespace Verbose.English

declare_syntax_cat maybeApplied
syntax term : maybeApplied
syntax term "applied to " term : maybeApplied
syntax term "applied to [" term,* "]" : maybeApplied
syntax term "applied to " term " using " term : maybeApplied
syntax term "applied to " term " using that " term : maybeApplied
syntax term "applied to " term " using [" term,* "]" : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM Term
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term applied to $x:term) => `($e $x)
| `(maybeApplied| $e:term applied to $x:term using $y) => `($e $x $y)
| `(maybeApplied| $e:term applied to $x:term using that $y) => `($e $x (strongAssumption% $y))
| `(maybeApplied| $e:term applied to $x:term using [$args:term,*]) => `($e $x $args*)
| `(maybeApplied| $e:term applied to [$args:term,*]) => `($e $args*)
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffEN
syntax (ppSpace colGt maybeTypedIdent)* : newStuffEN
syntax maybeTypedIdent "such that" (ppSpace colGt maybeTypedIdent)* : newStuffEN

def newStuffENToArray : TSyntax `newStuffEN → Array MaybeTypedIdent
| `(newStuffEN| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffEN| $x:maybeTypedIdent such that $news:maybeTypedIdent*) =>
    #[toMaybeTypedIdent x] ++ (Array.map toMaybeTypedIdent news)
| _ => #[]

declare_syntax_cat newFacts
syntax colGt namedType : newFacts
syntax colGt namedType " and "  colGt namedType : newFacts
syntax colGt namedType ", "  colGt namedType " and "  colGt namedType : newFacts

def newFactsToArray : TSyntax `newFacts → Array NamedType
| `(newFacts| $x:namedType) => #[toNamedType x]
| `(newFacts| $x:namedType and $y:namedType) =>
    #[toNamedType x, toNamedType y]
| `(newFacts| $x:namedType, $y:namedType and $z:namedType) =>
    #[toNamedType x, toNamedType y, toNamedType z]
| _ => #[]

def newFactsToTypeTerm : TSyntax `newFacts → MetaM Term
| `(newFacts| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFacts| $x:namedType and $y) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    `($xT ∧ $yT)
| `(newFacts| $x:namedType, $y:namedType and $z) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $yT ∧ $zT)
| _ => throwError "Could not convert the description of new facts into a term."

open Std Tactic Lean.Elab.Tactic.RCases in
def newFactsToRCasesPatt : TSyntax `newFacts → RCasesPatt
| `(newFacts| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFacts| $x:namedType and $y:namedType) => namedTypeListToRCasesPatt [x, y]
| `(newFacts|  $x:namedType, $y:namedType and $z:namedType) => namedTypeListToRCasesPatt [x, y, z]
| _ => default

declare_syntax_cat newObject
syntax maybeTypedIdent "such that" maybeTypedIdent : newObject
syntax maybeTypedIdent "such that" maybeTypedIdent colGt " and " maybeTypedIdent : newObject

def newObjectToTerm : TSyntax `newObject → MetaM Term
| `(newObject| $x:maybeTypedIdent such that $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObject| $x:maybeTypedIdent such that $new₁ and $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| _ => throwError "N'a pas pu convertir la description du nouvel object en un terme."

-- TODO: create helper functions for the values below
open Std Tactic Lean.Elab.Tactic.RCases in
def newObjectToRCasesPatt : TSyntax `newObject → RCasesPatt
| `(newObject| $x:maybeTypedIdent such that $new) => maybeTypedIdentListToRCasesPatt [x, new]
| `(newObject| $x:maybeTypedIdent such that $new₁ and $new₂) => maybeTypedIdentListToRCasesPatt [x, new₁, new₂]
| _ => default

declare_syntax_cat facts
syntax term : facts
syntax term " and " term : facts
syntax term ", " term " and " term : facts

def factsToArray : TSyntax `facts → Array Term
| `(facts| $x:term) => #[x]
| `(facts| $x:term and $y:term) => #[x, y]
| `(facts| $x:term, $y:term and $z:term) => #[x, y, z]
| _ => #[]

def arrayToFacts : Array Term → CoreM (TSyntax `facts)
| #[x] => `(facts| $x:term)
| #[x, y] => `(facts| $x:term and $y:term)
| #[x, y, z] => `(facts| $x:term, $y:term and $z:term)
| _ => default

end Verbose.English

/-- Convert an expression to a `maybeApplied` syntax object, in `MetaM`. -/
def Lean.Expr.toMaybeApplied (e : Expr) : MetaM (TSyntax `maybeApplied) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeApplied|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeApplied|$fnS:term applied to $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeApplied|$fnS:term applied to [$arr:term,*])
