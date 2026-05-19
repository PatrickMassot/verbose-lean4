import Verbose.Tactics.Common

open Lean

namespace Verbose.Spanish

declare_syntax_cat appliedToES
syntax "aplicado a " sepBy(term, " yy ") : appliedToES

def appliedToESTerm : TSyntax `appliedToES → Array Term
| `(appliedToES| aplicado a $[$args]yy*) => args
| _ => default -- This will never happen as long as nobody extends appliedToES

declare_syntax_cat usingStuffES
syntax " usando " sepBy(term, " yy ") : usingStuffES
syntax " usando que " term : usingStuffES

def usingStuffESToTerm : TSyntax `usingStuffES → Array Term
| `(usingStuffES| usando $[$args]yy*) => args
| `(usingStuffES| usando que $x) => #[Unhygienic.run `(strongAssumption% $x)]
| _ => default -- This will never happen as long as nobody extends appliedToES

declare_syntax_cat maybeAppliedES
syntax term (appliedToES)? (usingStuffES)? : maybeAppliedES

def maybeAppliedESToTerm : TSyntax `maybeAppliedES → MetaM Term
| `(maybeAppliedES| $e:term) => pure e
| `(maybeAppliedES| $e:term $args:appliedToES) => `($e $(appliedToESTerm args)*)
| `(maybeAppliedES| $e:term $args:usingStuffES) => `($e $(usingStuffESToTerm args)*)
| `(maybeAppliedES| $e:term $args:appliedToES $extras:usingStuffES) =>
  `($e $(appliedToESTerm args)* $(usingStuffESToTerm extras)*)
| _ => pure default -- This will never happen as long as nobody extends maybeAppliedES

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
yy the second one is its main arguments. When there is a third element, it is assumed
to be the type of a prop argument. -/
def listTermToMaybeApplied : List Term → MetaM (TSyntax `maybeAppliedES)
| [x] => `(maybeAppliedES|$x:term)
| [x, v] => `(maybeAppliedES|$x:term aplicado a $v)
| [x, v, z] => `(maybeAppliedES|$x:term aplicado a $v usando que $z)
| x::v::l => `(maybeAppliedES|$x:term aplicado a $v:term usando [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffES
syntax (ppSpace colGt maybeTypedIdent)* : newStuffES
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent : newStuffES
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent " yy "
       ppSpace colGt maybeTypedIdent : newStuffES

def newStuffESToArray : TSyntax `newStuffES → Array MaybeTypedIdent
| `(newStuffES| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffES| $x:maybeTypedIdent tal que $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuffES| $x:maybeTypedIdent tal que $v:maybeTypedIdent yy $z) =>
    Array.map toMaybeTypedIdent #[x, v, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatES : List MaybeTypedIdent → MetaM (TSyntax `newStuffES)
| [x] => do `(newStuffES| $(← x.stx):maybeTypedIdent)
| [x, z] => do `(newStuffES| $(← x.stx):maybeTypedIdent tal que $(← z.stx'))
| [x, z, v] => do `(newStuffES| $(← x.stx):maybeTypedIdent tal que $(← z.stx) yy $(← v.stx))
| _ => pure default

declare_syntax_cat newFactsES
syntax colGt namedType : newFactsES
syntax colGt namedType " yy "  colGt namedType : newFactsES
syntax colGt namedType ", "  colGt namedType " yy "  colGt namedType : newFactsES

def newFactsESToArray : TSyntax `newFactsES → Array NamedType
| `(newFactsES| $x:namedType) => #[toNamedType x]
| `(newFactsES| $x:namedType yy $v:namedType) =>
    #[toNamedType x, toNamedType v]
| `(newFactsES| $x:namedType, $v:namedType yy $z:namedType) =>
    #[toNamedType x, toNamedType v, toNamedType z]
| _ => #[]

def newFactsESToTypeTerm : TSyntax `newFactsES → MetaM Term
| `(newFactsES| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFactsES| $x:namedType yy $v) => do
    let xT ← namedTypeToTypeTerm x
    let vT ← namedTypeToTypeTerm v
    `($xT ∧ $vT)
| `(newFactsES| $x:namedType, $v:namedType yy $z) => do
    let xT ← namedTypeToTypeTerm x
    let vT ← namedTypeToTypeTerm v
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $vT ∧ $zT)
| _ => throwError "No se ha podido convertir la información dada en un término."

open Tactic Lean.Elab.Tactic.RCases in
def newFactsESToRCasesPatt : TSyntax `newFactsES → RCasesPatt
| `(newFactsES| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFactsES| $x:namedType yy $v:namedType) => namedTypeListToRCasesPatt [x, v]
| `(newFactsES|  $x:namedType, $v:namedType yy $z:namedType) => namedTypeListToRCasesPatt [x, v, z]
| _ => default

def listMaybeTypedIdentToNewFactsES : List MaybeTypedIdent → MetaM (TSyntax `newFactsES)
| [x] => do `(newFactsES| $(.mk (← x.stx)))
| [x, v] => do `(newFactsES| $(.mk (← x.stx).raw):namedType yy $(.mk (← v.stx)))
| [x, v, z] => do `(newFactsES| $(.mk (← x.stx)):namedType, $(.mk (← v.stx)) yy $(.mk (← z.stx)))
| _ => pure default

syntax talesQue := "tal que " <|> "tales que "

declare_syntax_cat newObjectES
syntax maybeTypedIdent "tal que " maybeTypedIdent : newObjectES
syntax maybeTypedIdent "tal que " maybeTypedIdent colGt " yy " maybeTypedIdent : newObjectES
syntax maybeTypedIdent "tal que " maybeTypedIdent ", " colGt maybeTypedIdent colGt " yy " maybeTypedIdent : newObjectES

syntax maybeTypedIdent " yy " maybeTypedIdent "tal que " maybeTypedIdent : newObjectES
syntax maybeTypedIdent " yy " maybeTypedIdent "tal que " maybeTypedIdent colGt " yy " maybeTypedIdent : newObjectES
syntax maybeTypedIdent " yy " maybeTypedIdent "tal que " maybeTypedIdent ", " colGt maybeTypedIdent colGt " yy " maybeTypedIdent : newObjectES

def newObjectESToTerm : TSyntax `newObjectES → MetaM Term
| `(newObjectES| $x:maybeTypedIdent tal que $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObjectES| $x:maybeTypedIdent tal que $new₁ yy $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| `(newObjectES| $x:maybeTypedIdent tal que $new₁, $new₂ yy $new₃) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    let new₃T := (toMaybeTypedIdent new₃).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T ∧ $new₃T)
| `(newObjectES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let v' ← maybeTypedIdentToExplicitBinder v
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), ∃ $(.mk v'), $newT)
| `(newObjectES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new₁ yy $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let v' ← maybeTypedIdentToExplicitBinder v
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), ∃ $(.mk v'), $new₁T ∧ $new₂T)
| `(newObjectES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new₁, $new₂ yy $new₃) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let v' ← maybeTypedIdentToExplicitBinder v
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    let new₃T := (toMaybeTypedIdent new₃).2.get!
    `(∃ $(.mk x'), ∃ $(.mk v'), $new₁T ∧ $new₂T ∧ $new₃T)
| _ => throwError "No se ha podido convertir la descripción del objeto nuevo en un término."

def newObjectESToMaybeTypedIdentList : TSyntax `newObjectES → List (TSyntax `maybeTypedIdent)
| `(newObjectES| $x:maybeTypedIdent tal que $new) => [x, new]
| `(newObjectES| $x:maybeTypedIdent tal que $new₁ yy $new₂) => [x, new₁, new₂]
| `(newObjectES| $x:maybeTypedIdent tal que $new₁, $new₂ yy $new₃) => [x, new₁, new₂, new₃]
| `(newObjectES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new) => [x, v, new]
| `(newObjectES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new₁ yy $new₂) => [x, v, new₁, new₂]
| `(newObjectES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new₁, $new₂ yy $new₃) => [x, v, new₁, new₂, new₃]
| _ => []


def newObjectESToArray : TSyntax `newObjectES → Array MaybeTypedIdent
| `(newObjectES| $x:maybeTypedIdent tal que $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newObjectES| $x:maybeTypedIdent tal que $v:maybeTypedIdent yy $z) =>
    Array.map toMaybeTypedIdent #[x, v, z]
| _ => #[]

open Tactic Lean.Elab.Tactic.RCases in
def newObjectESToRCasesPatt (newObj : TSyntax `newObjectES) : RCasesPatt :=
  maybeTypedIdentListToRCasesPatt <| newObjectESToMaybeTypedIdentList newObj

-- FIXME: the code below is ugly, written in a big hurry.
def listMaybeTypedIdentToNewObjectES : List MaybeTypedIdent → MetaM (TSyntax `newObjectES)
| [x, v] => do `(newObjectES| $(← x.stx):maybeTypedIdent tal que $(← v.stx'))
| [x, v, z] => do `(newObjectES| $(← x.stx):maybeTypedIdent tal que $(← v.stx) yy $(← z.stx))
| _ => pure default

declare_syntax_cat factsES
syntax term : factsES
syntax term " yy " term : factsES
syntax term ", " term " yy " term : factsES
syntax term ", " term ", " term " yy " term : factsES

def factsESToArray : TSyntax `factsES → Array Term
| `(factsES| $x:term) => #[x]
| `(factsES| $x:term yy $v:term) => #[x, v]
| `(factsES| $x:term, $v:term yy $z:term) => #[x, v, z]
| `(factsES| $x:term, $v:term, $z:term yy $w:term) => #[x, v, z, w]
| _ => #[]

def arrayToFactsES : Array Term → CoreM (TSyntax `factsES)
| #[x] => `(factsES| $x:term)
| #[x, v] => `(factsES| $x:term yy $v:term)
| #[x, v, z] => `(factsES| $x:term, $v:term yy $z:term)
| #[x, v, z, w] => `(factsES| $x:term, $v:term, $z:term yy $w:term)
| _ => default

def factsESToTypeTerm : TSyntax `factsES → MetaM Term
| `(factsES| $x:term) => `($x)
| `(factsES| $x:term yy $v) => `($x ∧ $v)
| `(factsES| $x:term, $v:term yy $z) => `($x ∧ $v ∧ $z)
| _ => throwError "No se ha podido convertir la descripción de la nueva información en un término."

/-- Convert an expression to a `maybeAppliedES` syntax object, in `MetaM`. -/
def _root_.Lean.Expr.toMaybeAppliedES (e : Expr) : MetaM (TSyntax `maybeAppliedES) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeAppliedES|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeAppliedES|$fnS:term aplicado a $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeAppliedES|$fnS:term aplicado a [$arr:term,*])

declare_syntax_cat newObjectNameLessES
syntax maybeTypedIdent "tal que " term : newObjectNameLessES
syntax maybeTypedIdent "tal que " term colGt " yy " term : newObjectNameLessES
syntax maybeTypedIdent "tal que " term ", " colGt term colGt " yy " term : newObjectNameLessES

syntax maybeTypedIdent " yy " maybeTypedIdent "tal que " term : newObjectNameLessES
syntax maybeTypedIdent " yy " maybeTypedIdent "tal que " term colGt " yy " term : newObjectNameLessES
syntax maybeTypedIdent " yy " maybeTypedIdent "tal que " term ", " colGt term colGt " yy " term : newObjectNameLessES

def newObjectNameLessESToLists : TSyntax `newObjectNameLessES → (List (TSyntax `maybeTypedIdent) × List Term)
| `(newObjectNameLessES| $x:maybeTypedIdent tal que $new) =>
  ([x], [new])
| `(newObjectNameLessES| $x:maybeTypedIdent tal que $new₁ yy $new₂) =>
  ([x], [new₁, new₂])
| `(newObjectNameLessES| $x:maybeTypedIdent tal que $new₁, $new₂ yy $new₃) =>
  ([x], [new₁, new₂, new₃])
| `(newObjectNameLessES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new) =>
  ([x, v], [new])
| `(newObjectNameLessES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new₁ yy $new₂) =>
  ([x, v], [new₁, new₂])
| `(newObjectNameLessES| $x:maybeTypedIdent yy $v:maybeTypedIdent tal que $new₁, $new₂ yy $new₃) =>
  ([x, v], [new₁, new₂, new₃])
| _ => default

def newObjectNameLessESToTerm (no : TSyntax `newObjectNameLessES) : MetaM Term :=
  let (xs, news) := newObjectNameLessESToLists no
  newObjNlToTerm xs news

def newObjectNameLessESToArray (no : TSyntax `newObjectNameLessES) : Array MaybeTypedIdent :=
  let (xs, news) := newObjectNameLessESToLists no
  newObjNlToArray xs news

open Tactic Lean.Elab.Tactic.RCases in
def newObjectNameLessESToRCasesPatt (no : TSyntax `newObjectNameLessES) : RCasesPatt :=
  let (xs, news) := newObjectNameLessESToLists no
  newObjNlToRCasesPatt xs news

def listMaybeTypedIdentToNewObjectNameLessES : List MaybeTypedIdent → MetaM (TSyntax `newObjectNameLessES)
| [(x, some t), (_, some s)] => do `(newObjectNameLessES| ($(mkIdent x):ident : $t) tal que $s)
| [(x, none), (_, some s)] => do `(newObjectNameLessES| $(mkIdent x):ident tal que $s)
| [(x, none), (_, some s), (_, some r)] => do `(newObjectNameLessES| $(mkIdent x):ident tal que $s yy $r)
| [(x, some t), (_, some s), (_, some r)] => do `(newObjectNameLessES| ($(mkIdent x):ident : $t) tal que $s yy $r)
| _ => pure default

implement_endpoint (lang := es) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"El nombre {n} ya está en uso"

implement_endpoint (lang := es) notDefEq (e val : MessageData) : CoreM MessageData :=
pure m!"El término {e}\n no es igual por definición a {val}"

implement_endpoint (lang := es) notAppConst : CoreM String :=
pure "No es la aplicación de una definición."

implement_endpoint (lang := es) cannotExpand : CoreM String :=
pure "No se ha podido expandir la cabeza del término."

implement_endpoint (lang := es) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"La afirmación {tgt} no parece directamente derivable de al menos alguna de las hipótesis."

implement_endpoint (lang := es) couldNotProve (goal : Format) : CoreM String :=
pure s!"No se pudo probar:\n{goal}"

implement_endpoint (lang := es) failedProofUsing (goal : Format) : CoreM String :=
pure s!"No se ha podido probar {goal}\n usando la información dada."
