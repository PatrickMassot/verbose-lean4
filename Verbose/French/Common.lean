import Verbose.Tactics.Common

open Lean

declare_syntax_cat maybeApplied
syntax term : maybeApplied
syntax term "appliqué à " term : maybeApplied
syntax term "appliqué à [" term,* "]" : maybeApplied
syntax term "appliqué à " term " en utilisant " term : maybeApplied
syntax term "appliqué à " term " en utilisant [" term,* "]" : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM Term
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term appliqué à $x:term) => `($e $x)
| `(maybeApplied| $e:term appliqué à $x:term en utilisant $y) => `($e $x $y)
| `(maybeApplied| $e:term appliqué à $x:term en utilisant [$args:term,*]) => `($e $x $args*)
| `(maybeApplied| $e:term appliqué à [$args:term,*]) => `($e $args*)
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuff
syntax (ppSpace colGt maybeTypedIdent)* : newStuff
syntax maybeTypedIdent "tel que" (ppSpace colGt maybeTypedIdent)* : newStuff

def newStuffToArray : TSyntax `newStuff → Array MaybeTypedIdent
| `(newStuff| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuff| $x:maybeTypedIdent tel que $news:maybeTypedIdent*) =>
    #[toMaybeTypedIdent x] ++ (Array.map toMaybeTypedIdent news)
| _ => #[]
