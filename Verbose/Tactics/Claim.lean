module

public meta import Verbose.Tactics.Lets

public meta section

open Lean Elab Tactic

def mkClaim (stmt : Term) (tac : Ident → TacticM Syntax) : TacticM Unit := do
  withMainContext do
  let e ← elabTerm stmt none
  let name := mkIdent (← mk_hyp_name stmt e)
  withRef stmt <| evalTactic (← tac name)


