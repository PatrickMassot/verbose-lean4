import Verbose.Tactics.Common

open Lean

namespace Verbose.English

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

declare_syntax_cat newStuffEN
syntax (ppSpace colGt maybeTypedIdent)* : newStuffEN
syntax maybeTypedIdent "such that" (ppSpace colGt maybeTypedIdent)* : newStuffEN

def newStuffENToArray : TSyntax `newStuffEN → Array MaybeTypedIdent
| `(newStuffEN| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffEN| $x:maybeTypedIdent such that $news:maybeTypedIdent*) =>
    #[toMaybeTypedIdent x] ++ (Array.map toMaybeTypedIdent news)
| _ => #[]

end Verbose.English
