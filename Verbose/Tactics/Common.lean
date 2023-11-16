import Lean

import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Tactic

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

def mkBinderIdent (n : Name) : CoreM (TSyntax ``binderIdent) :=
  `(binderIdent| $(mkIdent n):ident)

def elabTermEnsuringValue (t : Term) (val : Expr) : TermElabM Expr :=
  Term.withSynthesize do
  Term.withoutErrToSorry do
  let e ← Term.elabTerm t none
  -- The `withAssignableSyntheticOpaque` is to be able to assign ?_ metavariables
  unless ← withAssignableSyntheticOpaque <| isDefEq e val do
    throwError "Given term{indentD e}\nis not definitionally equal to the expected{
      ""}{indentD val}"
  return e
