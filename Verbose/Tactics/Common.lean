import Lean

import Std.Tactic.RCases
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

elab "checkName" name:ident : tactic => do
  checkName name.getId

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

def MaybeTypedIdent := Name × Option Term

instance : ToString MaybeTypedIdent where
  toString
  | (n, some t) => s!"({n} : {Syntax.prettyPrint t})"
  | (n, none) => s!"{n}"


open Std Tactic RCases

-- TODO: replace Syntax.missing by something smarter
def RCasesPattOfMaybeTypedIdent : MaybeTypedIdent → RCasesPatt
| (n, some pe) => RCasesPatt.typed Syntax.missing (RCasesPatt.one Syntax.missing  n) pe
| (n, none)    => RCasesPatt.one Syntax.missing n

declare_syntax_cat maybeTypedIdent
syntax ident : maybeTypedIdent
syntax "("ident " : " term")" : maybeTypedIdent
syntax ident " : " term : maybeTypedIdent

-- We could also use the less specific type `Syntax → MaybeTypedIdent`
def toMaybeTypedIdent : TSyntax `maybeTypedIdent → MaybeTypedIdent
| `(maybeTypedIdent| ($x:ident : $type:term)) => (x.getId, type)
| `(maybeTypedIdent| $x:ident : $type:term) => (x.getId, type)
| `(maybeTypedIdent| $x:ident) => (x.getId, none)
| _ => (Name.anonymous, none) -- This should never happen

def maybeTypedIdentToTerm : TSyntax `maybeTypedIdent → MetaM Term
| `(maybeTypedIdent| ($x:ident : $type:term)) => `(($x : $type))
| `(maybeTypedIdent| $x:ident : $type:term) => `(($x : $type))
| `(maybeTypedIdent| $x:ident) => `($x)
| _ => unreachable!

def maybeTypedIdentToRcasesPat : TSyntax `maybeTypedIdent → MetaM (TSyntax `Std.Tactic.RCases.rcasesPatLo)
| `(maybeTypedIdent| ($x:ident : $type:term)) => `(rcasesPatLo|$x)
| `(maybeTypedIdent| $x:ident : $type:term) => `(rcasesPatLo|$x)
| `(maybeTypedIdent| $x:ident) => `(rcasesPatLo|$x)
| _ => unreachable!

def ident_to_location (x : TSyntax `ident) : MetaM (TSyntax `Lean.Parser.Tactic.location) :=
`(location|at $(.mk #[x]):term*)

open Linarith in
/-- A version of the assumption tactic that also tries to run `linarith only [x]` for each local declaration `x`. -/
elab "strongAssumption" : tactic => do
  evalTactic (← `(tactic|assumption)) <|> withMainContext do
  let goal ← getMainGoal
  let target ← getMainTarget
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    try
      linarith true [ldecl.toExpr] {preprocessors := defaultPreprocessors} goal
      return
    catch _ => pure ()
  throwTacticEx `byAssumption (← getMainGoal)
    m!"The following does not seem to follow immediately from at most one local assumption: {indentExpr target}"

macro "strongAssumption%" x:term : term => `((by strongAssumption : $x))

/-- Given an expression whose head is the application of a defined constant,
return the expression obtained by unfolding the definition of this constant.
Otherwise return `none`. -/
def Lean.Expr.expandHeadFun (e : Expr) : MetaM (Option Expr) := do
  if e.isApp && e.getAppFn matches (.const ..) then
    e.withApp fun f args ↦ match f with
    | .const name us => do
      try
        let info ← getConstInfoDefn name
        return some <| info.value.instantiateLevelParams info.levelParams us |>.beta args
      catch _ => return none
    | _ => throwError "Not an application of a constant."
  else
    return none

/-- Given an expression whose head is the application of a defined constant,
return the expression obtained by unfolding the definition of this constant.
Otherwise throw an error. -/
def Lean.Expr.expandHeadFun! (e : Expr) : MetaM Expr := do
  if let some e' ← e.expandHeadFun then
    return e'
  else
    throwError "Cannot expand head."
