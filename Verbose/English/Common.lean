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
