import Lean
import Std.Tactic.RCases

import Verbose.Common

open Lean

open Lean.Parser.Tactic
open Lean Meta

def MaybeTypedIdent := Name × Option Term

open Lean Elab Tactic
open Option
open Std Tactic RCases

-- TODO: replace Syntax.missing by something smarter
def RCasesPattOfMaybeTypedIdent : MaybeTypedIdent → RCasesPatt
| (n, some pe) => RCasesPatt.typed Syntax.missing (RCasesPatt.one Syntax.missing  n) pe
| (n, none)    => RCasesPatt.one Syntax.missing n

def obtainTac (fact : Term) (news : Array MaybeTypedIdent) : TacticM Unit :=
do
  let orig_goal ← getMainGoal
  for new in news do
    checkName new.1
  let applied_fact_expr : Expr ← elabTerm fact none
  let news := Array.toList news
  match news with
  | [(name, stuff)] => do
    let type ← inferType applied_fact_expr
    if let some new := stuff then
      if not (← isDefEq (← elabTerm new type) type) then throwError "No way"
    let intermediate_goal ← orig_goal.assert name type (← elabTerm fact none)
    let (_, new_goal) ← intermediate_goal.intro1P
    replaceMainGoal [new_goal]
  | news =>
    let news_patt := news.map RCasesPattOfMaybeTypedIdent
    let new_goals ← rcases #[(none, fact)] (RCasesPatt.tuple Syntax.missing news_patt) (← getMainGoal)
    replaceMainGoal new_goals

declare_syntax_cat maybeTypedIdent
syntax ident : maybeTypedIdent
syntax "("ident ":" term")" : maybeTypedIdent

-- We could also use the less specific type `Syntax → MaybeTypedIdent`
def toMaybeTypedIdent : TSyntax `maybeTypedIdent → MaybeTypedIdent
| `(maybeTypedIdent| ($x:ident : $type:term)) => (x.getId, type)
| `(maybeTypedIdent| $x:ident) => (x.getId, none)
| _ => (Name.anonymous, none) -- This should never happen

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
