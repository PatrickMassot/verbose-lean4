import Std.Tactic.RCases

import Verbose.Tactics.Common
import Verbose.Tactics.MaybeTypedIdent

open Lean Elab Tactic Meta
open Std Tactic RCases


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
