import Verbose.Tactics.Common

open Lean Parser Elab Tactic

def computeAtGoalTac : TacticM Unit := do
  evalTactic (← `(tactic|iterate 3 (first | ring_nf | abel | norm_num)))
