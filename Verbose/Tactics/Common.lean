import Lean
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Data.Real.Basic

import Verbose.Infrastructure.Extension
import Verbose.Infrastructure.Multilingual

open Lean Parser Tactic Meta Elab Tactic Option

/-! # Infrastructure common to several tactics

This file gathers meta-programming functions that are used by several tactics
as well as syntactic constructions that are language-independent.

It also feature the `strongAssumption` tactic and the associated term elaborator.
They are used as building blocks for several tactics.

## Parsing molecules

By Kyle Miller
-/

section

/--
Splits a "molecule" into atoms. For example,
```
splitMolecule "  a b  c " = #["  a ", "b  ", "c "]
```
-/
partial def splitMolecule (s : String) : Array String :=
  let it := s.mkIterator
  go #[] it (it.find (!·.isWhitespace))
where
  go (atoms : Array String) (left right : String.Iterator) : Array String :=
    let right := right |>.find (·.isWhitespace) |>.find (!·.isWhitespace)
    if left == right then
      atoms
    else
      let atoms := atoms.push (left.extract right)
      go atoms right right

def isStxMolecule (p : Syntax) : Bool :=
  p.isOfKind ``Lean.Parser.Syntax.atom
    && if let some atom := p[0].isStrLit? then atom.trim.any Char.isWhitespace else false

def expandStxMolecules? (s : Syntax) : MacroM (Option Syntax) := do
  unless (s.find? isStxMolecule).isSome do
    return none
  s.replaceM fun p => do
    if isStxMolecule p then
      if let some s := p[0].isStrLit? then
        withRef p do
          let atomStrings := splitMolecule s
          let atoms ← atomStrings.mapM fun atomString => `(stx| $(quote atomString):str)
          `(stx| group($[$atoms]*))
      else
        Macro.throwUnsupported
    else
      return none

def expandStxMolecules : Lean.Macro := fun s => do
  (← expandStxMolecules? s).getDM Macro.throwUnsupported

attribute [macro Lean.Parser.Command.syntax] expandStxMolecules
attribute [macro Lean.Parser.Command.syntaxAbbrev] expandStxMolecules

end
/-
## Missing general purpose functions.

Those functions have nothing to do with Verbose Lean and could be in core Lean
(and maybe some of them are there somewhere but I couldn't find them).
-/

/-- Return a name that is not used in the local context of the given goal and looks like
the suggestion. If the suggestion is not available then the produced name will
have a numeric suffix. -/
def Lean.MVarId.getUnusedUserName {n : Type → Type} [MonadControlT MetaM n] [MonadLiftT MetaM n]
    [Monad n] (goal : MVarId) (suggestion : Name) : n Name := do
  return (← goal.getDecl).lctx.getUnusedUserName suggestion

register_endpoint nameAlreadyUsed (n : Name) : CoreM String

/-- Check whether a name is available in the current local context. -/
def checkName (n : Name) : TacticM Unit := do
if (← getLCtx).usesUserName n then
  throwError ← nameAlreadyUsed n
else pure ()

/-- Check whether a name is available. Is used by other tactics defined as macros. -/
elab "checkName" name:ident : tactic => do
  checkName name.getId

/-- Produces a `binderIdent` syntax from the given name. -/
def mkBinderIdent (n : Name) : CoreM (TSyntax ``binderIdent) :=
  `(binderIdent| $(mkIdent n):ident)

register_endpoint notDefEq (e val : MessageData) : CoreM MessageData

/-- Elaborate the given term and throw an error if its value is not definitionaly
equal to the given value expression. -/
def elabTermEnsuringValue (t : Term) (val : Expr) : TermElabM Expr :=
  Term.withSynthesize do
  Term.withoutErrToSorry do
  let e ← Term.elabTerm t none
  -- The `withAssignableSyntheticOpaque` is to be able to assign ?_ metavariables
  unless ← withAssignableSyntheticOpaque <| isDefEq e val do
    throwError ← notDefEq (indentD e) (indentD val)
  return e

def ident_to_location (x : TSyntax `ident) : MetaM (TSyntax `Lean.Parser.Tactic.location) :=
`(location|at $(.mk #[x]):term*)

register_endpoint notAppConst : CoreM String

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
    | _ => do throwError ← notAppConst
  else
    return none

register_endpoint cannotExpand : CoreM String

/-- Given an expression whose head is the application of a defined constant,
return the expression obtained by unfolding the definition of this constant.
Otherwise throw an error. -/
def Lean.Expr.expandHeadFun! (e : Expr) : MetaM Expr := do
  if let some e' ← e.expandHeadFun then
    return e'
  else
    throwError ← cannotExpand

/-! ## Common syntax categories and their conversions to other syntax categories -/

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

def toMaybeTypedIdent : TSyntax `maybeTypedIdent → MaybeTypedIdent
| `(maybeTypedIdent| ($x:ident : $type:term)) => (x.getId, type)
| `(maybeTypedIdent| $x:ident : $type:term) => (x.getId, type)
| `(maybeTypedIdent| $x:ident) => (x.getId, none)
| _ => (Name.anonymous, none) -- This should never happen

def MaybeTypedIdent.stx : MaybeTypedIdent → MetaM (TSyntax `maybeTypedIdent)
| (x, some type) => `(maybeTypedIdent| ($(mkIdent x):ident : $type:term))
| (x, none) => `(maybeTypedIdent| $(mkIdent x):ident)

def MaybeTypedIdent.stx' : MaybeTypedIdent → MetaM (TSyntax `maybeTypedIdent)
| (x, some type) => `(maybeTypedIdent| $(mkIdent x):ident : $type:term)
| (x, none) => `(maybeTypedIdent| $(mkIdent x):ident)

def maybeTypedIdentToTerm : TSyntax `maybeTypedIdent → MetaM Term
| `(maybeTypedIdent| ($x:ident : $type:term)) => `(($x : $type))
| `(maybeTypedIdent| $x:ident : $type:term) => `(($x : $type))
| `(maybeTypedIdent| $x:ident) => `($x)
| _ => unreachable!

def maybeTypedIdentToExplicitBinder : TSyntax `maybeTypedIdent → MetaM (TSyntax `Lean.explicitBinders)
| `(maybeTypedIdent| ($x:ident : $type:term)) => `(explicitBinders|($x:ident : $type))
| `(maybeTypedIdent| $x:ident : $type:term) => `(explicitBinders|($x:ident : $type))
| `(maybeTypedIdent| $x:ident) => `(explicitBinders|$x:ident)
| _ => unreachable!

def maybeTypedIdentToRcasesPat : TSyntax `maybeTypedIdent → MetaM (TSyntax `Lean.Parser.Tactic.rcasesPatLo)
| `(maybeTypedIdent| ($x:ident : $_type:term)) => `(rcasesPatLo|$x)
| `(maybeTypedIdent| $x:ident : $_type:term) => `(rcasesPatLo|$x)
| `(maybeTypedIdent| $x:ident) => `(rcasesPatLo|$x)
| _ => unreachable!

def maybeTypedIdentListToRCasesPatt : List (TSyntax `maybeTypedIdent) → RCasesPatt
| [] => default -- should not happen
| [x] => RCasesPattOfMaybeTypedIdent (toMaybeTypedIdent x)
| l => RCasesPatt.tuple Syntax.missing <| l.map (RCasesPattOfMaybeTypedIdent ∘ toMaybeTypedIdent)

declare_syntax_cat namedType
syntax "("ident " : " term")" : namedType
syntax ident " : " term : namedType

def NamedType := Name × Term deriving Inhabited

def toNamedType : TSyntax `namedType → NamedType
| `(namedType| ($x:ident : $type:term)) => (x.getId, type)
| `(namedType| $x:ident : $type:term) => (x.getId, type)
| _ => default -- This should never happen

def namedTypeToTerm : TSyntax `namedType → MetaM Term
| `(namedType| ($x:ident : $type:term)) => `(($x : $type))
| `(namedType| $x:ident : $type:term) => `(($x : $type))
| _ => unreachable!

def namedTypeToTypeTerm : TSyntax `namedType → MetaM Term
| `(namedType| ($_x:ident : $type:term)) => `($type)
| `(namedType| $_x:ident : $type:term) => `($type)
| _ => unreachable!

def namedTypeToRcasesPat : TSyntax `namedType → MetaM (TSyntax `Lean.Parser.Tactic.rcasesPatLo)
| `(namedType| ($x:ident : $_type:term)) => `(rcasesPatLo|$x)
| `(namedType| $x:ident : $_type:term) => `(rcasesPatLo|$x)
| _ => unreachable!

def NamedType.RCasesPatt : NamedType → RCasesPatt
| (n, pe) => RCasesPatt.typed Syntax.missing (RCasesPatt.one Syntax.missing  n) pe

def namedTypeListToRCasesPatt : List (TSyntax `namedType) → RCasesPatt
| [] => default -- should not happen
| [x] => (toNamedType x).RCasesPatt
| l => RCasesPatt.tuple Syntax.missing <| l.map (NamedType.RCasesPatt ∘ toNamedType)

/-! ## The strongAssumption tactic and term elaborator -/

register_endpoint doesntFollow (tgt : MessageData) : CoreM MessageData

/-- A version of the `assumption` tactic that also try `apply h` for each local assumption `h`. -/
def assumption' : TacticM Unit := do
  let goal ← getMainGoal
  withAssignableSyntheticOpaque do
  let target ← goal.getType
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    try
      let newGoals ← goal.apply ldecl.toExpr
      if newGoals matches [] then
        return
    catch _ => pure ()
  throwTacticEx `byAssumption goal (← doesntFollow (indentExpr target))


open Linarith in
/-- A version of the assumption tactic that also tries to run `linarith only [x]` for each local declaration `x`. -/
elab "strongAssumption" : tactic => do
  assumption' <|> withMainContext do
  let goal ← getMainGoal
  let target ← getMainTarget
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    try
      linarith true [ldecl.toExpr] {preprocessors := defaultPreprocessors} goal
      return
    catch _ => pure ()
  throwTacticEx `byAssumption (← getMainGoal) (← doesntFollow (indentExpr target))

macro "strongAssumption%" x:term : term => `((by strongAssumption : $x))

initialize registerTraceClass `Verbose
