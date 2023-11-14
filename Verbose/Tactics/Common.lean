import Lean

open Lean
open Lean.Parser.Tactic
open Lean Meta
open Lean Elab Tactic
open Option

/-- Check whether a name is available. -/
def checkName (n : Name) : TacticM Unit := do
if (← getLCtx).usesUserName n then
  throwError "The name {n} is already used"
else pure ()
