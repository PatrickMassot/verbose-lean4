import Verbose.Tactics.Common

open Lean

declare_syntax_cat maybeApplied
syntax term : maybeApplied
syntax term "applied to " term : maybeApplied
syntax term "applied to [" term,* "]" : maybeApplied
syntax term "applied to " term " using " term : maybeApplied
syntax term "applied to " term " using [" term,* "]" : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM Term
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term applied to $x:term) => `($e $x)
| `(maybeApplied| $e:term applied to $x:term using $y) => `($e $x $y)
| `(maybeApplied| $e:term applied to $x:term using [$args:term,*]) => `($e $x $args*)
| `(maybeApplied| $e:term applied to [$args:term,*]) => `($e $args*)
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuff
syntax (ppSpace colGt maybeTypedIdent)* : newStuff
syntax maybeTypedIdent "such that" (ppSpace colGt maybeTypedIdent)* : newStuff

def newStuffToArray : TSyntax `newStuff → Array MaybeTypedIdent
| `(newStuff| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuff| $x:maybeTypedIdent such that $news:maybeTypedIdent*) =>
    #[toMaybeTypedIdent x] ++ (Array.map toMaybeTypedIdent news)
| _ => #[]
