import Verbose.Tactics.Common

open Lean

namespace Verbose.French

declare_syntax_cat maybeAppliedFR
syntax term : maybeAppliedFR
syntax term "appliqué à " term : maybeAppliedFR
syntax term "appliqué à [" term,* "]" : maybeAppliedFR
syntax term "appliqué à " term " en utilisant " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant que " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant [" term,* "]" : maybeAppliedFR

def maybeAppliedFRToTerm : TSyntax `maybeAppliedFR → MetaM Term
| `(maybeAppliedFR| $e:term) => pure e
| `(maybeAppliedFR| $e:term appliqué à $x:term) => `($e $x)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant $y) => `($e $x $y)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant que $y) => `($e $x (strongAssumption% $y))
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant [$args:term,*]) => `($e $x $args*)
| `(maybeAppliedFR| $e:term appliqué à [$args:term,*]) => `($e $args*)
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffFR
syntax (ppSpace colGt maybeTypedIdent)* : newStuffFR
syntax maybeTypedIdent "tel que" (ppSpace colGt maybeTypedIdent)* : newStuffFR

def newStuffFRToArray : TSyntax `newStuffFR → Array MaybeTypedIdent
| `(newStuffFR| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffFR| $x:maybeTypedIdent tel que $news:maybeTypedIdent*) =>
    #[toMaybeTypedIdent x] ++ (Array.map toMaybeTypedIdent news)
| _ => #[]

declare_syntax_cat newObjectFR
syntax maybeTypedIdent "tel que" maybeTypedIdent : newObjectFR
syntax maybeTypedIdent "tel que" maybeTypedIdent colGt " et " maybeTypedIdent : newObjectFR

def newObjectFRToTerm : TSyntax `newObjectFR → MetaM Term
| `(newObjectFR| $x:maybeTypedIdent tel que $new) => do
    let x' ← maybeTypedIdentToTerm x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObjectFR| $x:maybeTypedIdent tel que $new₁ et $new₂) => do
    let x' ← maybeTypedIdentToTerm x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| _ => throwError "N'a pas pu convertir la description du nouvel object en un terme."

open Std Tactic RCases in
def newObjectFRToRCasesPatt : TSyntax `newObjectFR → RCasesPatt
| `(newObjectFR| $x:maybeTypedIdent tel que $new) => RCasesPatt.tuple Syntax.missing <| [x, new].map (RCasesPattOfMaybeTypedIdent ∘ toMaybeTypedIdent)
| `(newObjectFR| $x:maybeTypedIdent tel que $new₁ et $new₂) => RCasesPatt.tuple Syntax.missing  <| [x, new₁, new₂].map (RCasesPattOfMaybeTypedIdent ∘ toMaybeTypedIdent)
| _ => default

-- TODO: create helper functions for the values below
def newObjectFRTorcasesPat : TSyntax `newObjectFR → MetaM (TSyntax `rcasesPat)
| `(newObjectFR| $x:maybeTypedIdent tel que $new) => do `(rcasesPat|⟨$(← maybeTypedIdentToRcasesPat x), $(← maybeTypedIdentToRcasesPat new)⟩)
| `(newObjectFR| $x:maybeTypedIdent tel que $new₁ et $new₂) => do `(rcasesPat|⟨$(← maybeTypedIdentToRcasesPat x), $(← maybeTypedIdentToRcasesPat new₁), $(← maybeTypedIdentToRcasesPat new₂)⟩)
| _ => default

declare_syntax_cat factsFR
syntax term : factsFR
syntax term " et " term : factsFR
syntax term ", " term " et " term : factsFR

def factsFRToArray: TSyntax `factsFR → Array Term
| `(factsFR| $x:term) => #[x]
| `(factsFR| $x:term et $y:term) => #[x, y]
| `(factsFR| $x:term, $y:term et $z:term) => #[x, y, z]
| _ => #[]

-- TODO: create helper functions for the values below
def factsFRToSolveByElimArgs: TSyntax `factsFR → MetaM (TSyntax `Std.Tactic.SolveByElim.args)
| `(factsFR| $x:term) => `(Std.Tactic.SolveByElim.args| [strongAssumption% $x:term])
| `(factsFR| $x:term et $y:term) =>  `(Std.Tactic.SolveByElim.args| [strongAssumption% $x:term, strongAssumption% $y:term])
| `(factsFR| $x:term, $y:term et $z:term) => `(Std.Tactic.SolveByElim.args| [strongAssumption% $x:term, strongAssumption% $y:term, strongAssumption% $z:term])
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
