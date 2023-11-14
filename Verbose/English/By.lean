import Verbose.Tactics.By

open Lean

declare_syntax_cat maybeApplied
syntax term : maybeApplied
syntax term "applied to" term : maybeApplied
syntax term "applied to [" term,* "]" : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM Term
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term applied to $x:term) => `($e $x)
| `(maybeApplied| $e:term applied to [$args:term,*]) => `($e $args*)
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuff
syntax maybeTypedIdent : newStuff
syntax maybeTypedIdent "such that" maybeTypedIdent,* : newStuff

def newStuffToArray : TSyntax `newStuff → Array MaybeTypedIdent
| `(newStuff| $x:maybeTypedIdent) => #[toMaybeTypedIdent x]
| `(newStuff| $x:maybeTypedIdent such that $news:maybeTypedIdent,*) =>
    #[toMaybeTypedIdent x] ++ (Array.map toMaybeTypedIdent news)
| _ => #[]

elab "By " e:maybeApplied "we get " colGt news:newStuff : tactic => do
obtainTac (← maybeAppliedToTerm e)  (newStuffToArray news)

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  By h applied to 0 we get h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  --rcases h 0 0 with (h₀ : P 0 0)
  By h applied to [0, 0] we get (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  By h we get k such that (H : n = 2*k)
  trivial

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  By h we get k such that H
  trivial
