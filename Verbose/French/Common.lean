import Verbose.Tactics.Common

open Lean

namespace Verbose.French

declare_syntax_cat maybeAppliedFR
syntax term : maybeAppliedFR
syntax term "appliqué à " term : maybeAppliedFR
syntax term "appliqué à [" term,* "]" : maybeAppliedFR
syntax term "appliqué à " term " en utilisant " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant [" term,* "]" : maybeAppliedFR

def maybeAppliedFRToTerm : TSyntax `maybeAppliedFR → MetaM Term
| `(maybeAppliedFR| $e:term) => pure e
| `(maybeAppliedFR| $e:term appliqué à $x:term) => `($e $x)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant $y) => `($e $x $y)
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
