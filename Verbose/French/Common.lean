import Verbose.Tactics.Common

open Lean

namespace Verbose.French

declare_syntax_cat appliedToFR
syntax "appliqué à " sepBy(term, " et ") : appliedToFR

def appliedToFRTerm : TSyntax `appliedToFR → Array Term
| `(appliedToFR| appliqué à $[$args]et*) => args
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat usingStuffFR
syntax " en utilisant " sepBy(term, " et ") : usingStuffFR
syntax " en utilisant que " term : usingStuffFR

def usingStuffFRToTerm : TSyntax `usingStuffFR → Array Term
| `(usingStuffFR| en utilisant $[$args]et*) => args
| `(usingStuffFR| en utilisant que $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends appliedTo

declare_syntax_cat maybeAppliedFR
syntax term (appliedToFR)? (usingStuffFR)? : maybeAppliedFR

def maybeAppliedFRToTerm : TSyntax `maybeAppliedFR → MetaM Term
| `(maybeAppliedFR| $e:term) => pure e
| `(maybeAppliedFR| $e:term $args:appliedToFR) => `($e $(appliedToFRTerm args)*)
| `(maybeAppliedFR| $e:term $args:usingStuffFR) => `($e $(usingStuffFRToTerm args)*)
| `(maybeAppliedFR| $e:term $args:appliedToFR $extras:usingStuffFR) =>
  `($e $(appliedToFRTerm args)* $(usingStuffFRToTerm extras)*)
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments. When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeApplied : List Term → MetaM (TSyntax `maybeAppliedFR)
| [x] => `(maybeAppliedFR|$x:term)
| [x, y] => `(maybeAppliedFR|$x:term appliqué à $y)
| [x, y, z] => `(maybeAppliedFR|$x:term appliqué à $y en utilisant que $z)
| x::y::l => `(maybeAppliedFR|$x:term appliqué à $y:term en utilisant que [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffFR
syntax (ppSpace colGt maybeTypedIdent)* : newStuffFR
syntax maybeTypedIdent "tel que" ppSpace colGt maybeTypedIdent : newStuffFR
syntax maybeTypedIdent "tel que" ppSpace colGt maybeTypedIdent " et " ppSpace colGt maybeTypedIdent : newStuffFR

def newStuffFRToArray : TSyntax `newStuffFR → Array MaybeTypedIdent
| `(newStuffFR| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffFR| $x:maybeTypedIdent tel que $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuffFR| $x:maybeTypedIdent tel que $y:maybeTypedIdent et $z) =>
    Array.map toMaybeTypedIdent #[x, y, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatFR : List MaybeTypedIdent → MetaM (TSyntax `newStuffFR)
| [x] => do `(newStuffFR| $(← x.stx):maybeTypedIdent)
| [x, y] => do `(newStuffFR| $(← x.stx):maybeTypedIdent tel que $(← y.stx'))
| [x, y, z] => do `(newStuffFR| $(← x.stx):maybeTypedIdent tel que $(← y.stx) et $(← z.stx))
| _ => pure default

declare_syntax_cat newFactsFR
syntax colGt namedType : newFactsFR
syntax colGt namedType " et "  colGt namedType : newFactsFR
syntax colGt namedType ", "  colGt namedType " et "  colGt namedType : newFactsFR

def newFactsFRToArray : TSyntax `newFactsFR → Array NamedType
| `(newFactsFR| $x:namedType) => #[toNamedType x]
| `(newFactsFR| $x:namedType et $y:namedType) =>
    #[toNamedType x, toNamedType y]
| `(newFactsFR| $x:namedType, $y:namedType et $z:namedType) =>
    #[toNamedType x, toNamedType y, toNamedType z]
| _ => #[]

def newFactsFRToTypeTerm : TSyntax `newFactsFR → MetaM Term
| `(newFactsFR| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFactsFR| $x:namedType et $y) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    `($xT ∧ $yT)
| `(newFactsFR| $x:namedType, $y:namedType et $z) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $yT ∧ $zT)
| _ => throwError "N'a pas pu convertir la description des nouveaux faits en un terme."

open Tactic Lean.Elab.Tactic.RCases in
def newFactsFRToRCasesPatt : TSyntax `newFactsFR → RCasesPatt
| `(newFactsFR| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFactsFR| $x:namedType et $y:namedType) => namedTypeListToRCasesPatt [x, y]
| `(newFactsFR|  $x:namedType, $y:namedType et $z:namedType) => namedTypeListToRCasesPatt [x, y, z]
| _ => default

def listMaybeTypedIdentToNewFactsFR : List MaybeTypedIdent → MetaM (TSyntax `newFactsFR)
| [x] => do `(newFactsFR| $(.mk (← x.stx)))
| [x, y] => do `(newFactsFR| $(.mk (← x.stx).raw):namedType et $(.mk (← y.stx)))
| [x, y, z] => do `(newFactsFR| $(.mk (← x.stx)):namedType, $(.mk (← y.stx)) et $(.mk (← z.stx)))
| _ => pure default

declare_syntax_cat newObjectFR
syntax maybeTypedIdent "tel que " maybeTypedIdent : newObjectFR
syntax maybeTypedIdent "tel que " maybeTypedIdent colGt " et " maybeTypedIdent : newObjectFR

def newObjectFRToTerm : TSyntax `newObjectFR → MetaM Term
| `(newObjectFR| $x:maybeTypedIdent tel que $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObjectFR| $x:maybeTypedIdent tel que $new₁ et $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| _ => throwError "N'a pas pu convertir la description du nouvel object en un terme."

-- TODO: create helper functions for the values below
open Tactic Lean.Elab.Tactic.RCases in
def newObjectFRToRCasesPatt : TSyntax `newObjectFR → RCasesPatt
| `(newObjectFR| $x:maybeTypedIdent tel que $new) => maybeTypedIdentListToRCasesPatt [x, new]
| `(newObjectFR| $x:maybeTypedIdent tel que $new₁ et $new₂) => maybeTypedIdentListToRCasesPatt [x, new₁, new₂]
| _ => default

-- FIXME: the code below is ugly, written in a big hurry.
def listMaybeTypedIdentToNewObjectFR : List MaybeTypedIdent → MetaM (TSyntax `newObjectFR)
| [x, y] => do `(newObjectFR| $(← x.stx):maybeTypedIdent tel que $(← y.stx'))
| [x, y, z] => do `(newObjectFR| $(← x.stx):maybeTypedIdent tel que $(← y.stx) et $(← z.stx))
| _ => pure default

declare_syntax_cat factsFR
syntax term : factsFR
syntax term " et " term : factsFR
syntax term ", " term " et " term : factsFR
syntax term ", " term ", " term " et " term : factsFR

def factsFRToArray : TSyntax `factsFR → Array Term
| `(factsFR| $x:term) => #[x]
| `(factsFR| $x:term et $y:term) => #[x, y]
| `(factsFR| $x:term, $y:term et $z:term) => #[x, y, z]
| `(factsFR| $x:term, $y:term, $z:term et $w:term) => #[x, y, z, w]
| _ => #[]

def arrayToFactsFR : Array Term → CoreM (TSyntax `factsFR)
| #[x] => `(factsFR| $x:term)
| #[x, y] => `(factsFR| $x:term et $y:term)
| #[x, y, z] => `(factsFR| $x:term, $y:term et $z:term)
| #[x, y, z, w] => `(factsFR| $x:term, $y:term, $z:term et $w:term)
| _ => default

end Verbose.French

/-- Convert an expression to a `maybeAppliedFR` syntax object, in `MetaM`. -/
def Lean.Expr.toMaybeAppliedFR (e : Expr) : MetaM (TSyntax `maybeAppliedFR) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeAppliedFR|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeAppliedFR|$fnS:term appliqué à $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeAppliedFR|$fnS:term appliqué à [$arr:term,*])

implement_endpoint (lang := fr) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"Le nom {n} est déjà utilisé."

implement_endpoint (lang := fr) notDefEq (e val : MessageData) : CoreM MessageData :=
pure m!"Le terme fourni{e}\nn’est pas égal par définition à celui attendu{val}"

implement_endpoint (lang := fr) notAppConst : CoreM String :=
pure "Ceci n’est pas l’application d’une définition."

implement_endpoint (lang := fr) cannotExpand : CoreM String :=
pure "Impossible de déplier la définition du symbole de tête."

implement_endpoint (lang := fr) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"L’affirmation {tgt} ne semble pas découler directement d’au plus une hypothèse locale."

implement_endpoint (lang := fr) couldNotProve (goal : Format) : CoreM String :=
pure s!"La justification a échoué :\n{goal}"

implement_endpoint (lang := fr) failedProofUsing (goal : Format) : CoreM String :=
pure s!"La justification en utilisant les faits fournis a échoué :\n{goal}"
