import Verbose.Tactics.Common

open Lean

namespace Verbose.English

declare_syntax_cat appliedTo
syntax "applied to " sepBy(term, "and") : appliedTo

def appliedToTerm : TSyntax `appliedTo → Array Term
| `(appliedTo| applied to $[$args]and*) => args
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat usingStuff
syntax " using " sepBy(term, "and") : usingStuff
syntax " using that " term : usingStuff

def usingStuffToTerm : TSyntax `usingStuff → Array Term
| `(usingStuff| using $[$args]and*) => args
| `(usingStuff| using that $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat maybeApplied
syntax term (appliedTo)? (usingStuff)? : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM Term
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term $args:appliedTo) => `($e $(appliedToTerm args)*)
| `(maybeApplied| $e:term $args:usingStuff) => `($e $(usingStuffToTerm args)*)
| `(maybeApplied| $e:term $args:appliedTo $extras:usingStuff) =>
  `($e $(appliedToTerm args)* $(usingStuffToTerm extras)*)
| _ => pure default -- This will never happen as long as nobody extends maybeApplied

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments. When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeApplied : List Term → MetaM (TSyntax `maybeApplied)
| [x] => `(maybeApplied|$x:term)
| [x, y] => `(maybeApplied|$x:term applied to $y)
| [x, y, z] => `(maybeApplied|$x:term applied to $y using that $z)
| x::y::l => `(maybeApplied|$x:term applied to $y:term using [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuff
syntax (ppSpace colGt maybeTypedIdent)* : newStuff
syntax maybeTypedIdent "such that" ppSpace colGt maybeTypedIdent : newStuff
syntax maybeTypedIdent "such that" ppSpace colGt maybeTypedIdent " and "
       ppSpace colGt maybeTypedIdent : newStuff

def newStuffToArray : TSyntax `newStuff → Array MaybeTypedIdent
| `(newStuff| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuff| $x:maybeTypedIdent such that $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuff| $x:maybeTypedIdent such that $y:maybeTypedIdent and $z) =>
    Array.map toMaybeTypedIdent #[x, y, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatEN : List MaybeTypedIdent → MetaM (TSyntax `newStuff)
| [x] => do `(newStuff| $(← x.stx):maybeTypedIdent)
| [x, y] => do `(newStuff| $(← x.stx):maybeTypedIdent such that $(← y.stx'))
| [x, y, z] => do `(newStuff| $(← x.stx):maybeTypedIdent such that $(← y.stx) and $(← z.stx))
| _ => pure default

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

open Tactic Lean.Elab.Tactic.RCases in
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
| _ => throwError "Could not convert the new object description into a term."

-- TODO: create helper functions for the values below
open Tactic Lean.Elab.Tactic.RCases in
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

implement_endpoint (lang := en) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"The name {n} is already used"

implement_endpoint (lang := en) notDefEq (e val : MessageData) : CoreM MessageData :=
pure m!"Given term{e}\nis not definitionally equal to the expected{val}"

implement_endpoint (lang := en) notAppConst : CoreM String :=
pure "Not an application of a definition."

implement_endpoint (lang := en) cannotExpand : CoreM String :=
pure "Cannot expand head."

implement_endpoint (lang := en) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"The following does not seem to follow immediately from at most one local assumption: {tgt}"
