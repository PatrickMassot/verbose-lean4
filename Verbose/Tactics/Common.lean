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

By Kyle Miller and David Thrane Christiansen
-/

section

/-- Always mark these atoms as non-reserved, so they can be used as identifiers. -/
def dontReserve : List String := ["a"]

/--
Splits a "molecule" into atoms. For example,
`splitMolecule "  a b  c " = #["  a ", "b  ", "c "]`
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
          if h : atomStrings.size > 0 then
            if atomStrings[0].trim ∈ dontReserve then
              Macro.throwErrorAt p
                s!"First contained atom is '{atomStrings[0].trim}', which shouldn't be reserved"
            let firstAtom ← `(stx|$(quote atomStrings[0]):str)
            let restAtoms ← (atomStrings.extract 1 atomStrings.size).mapM fun atomString =>
              if atomString.trim ∈ dontReserve then
                `(stx| &$(quote atomString):str)
              else `(stx| $(quote atomString):str)
            `(stx| group($firstAtom $[$restAtoms]*))
          else return none
      else
        Macro.throwUnsupported
    else
      return none

def expandStxMolecules : Lean.Macro := fun s => do
  (← expandStxMolecules? s).getDM Macro.throwUnsupported

attribute [macro Lean.Parser.Command.syntax] expandStxMolecules
attribute [macro Lean.Parser.Command.syntaxAbbrev] expandStxMolecules

def isNotationItemMolecule (p : Syntax) : Bool :=
  if let some atom := p.isStrLit? then atom.trim.any Char.isWhitespace else false

/-
@[builtin_command_parser] def «notation»    := leading_parser
  optional docComment >> optional Term.«attributes» >> Term.attrKind >>
  "notation" >> optPrecedence >> optNamedName >> optNamedPrio >> many notationItem >> darrow >> termParser

item 7 is the `many notationItem`
-/
def expandNotationMolecules : Lean.Macro := fun s => do
  let items := s[7].getArgs
  unless items.any isNotationItemMolecule do
    Macro.throwUnsupported
  let mut items' : Array Syntax := #[]
  for item in items do
    if let some s := item.isStrLit? then
      for atom in splitMolecule s do
        items' := items'.push <| ← withRef item `(Command.notationItem| $(quote atom):str)
    else
      items' := items'.push item
  return s.setArg 7 (mkNullNode items')

attribute [macro Lean.Parser.Command.notation] expandNotationMolecules

def isNotation3ItemMolecule (p : Syntax) : Bool :=
  if let some atom := p[0].isStrLit? then atom.trim.any Char.isWhitespace else false

def expandNotation3Molecules : Lean.Macro := fun s => do
  let items := s[8].getArgs
  unless items.any isNotation3ItemMolecule do
    Macro.throwUnsupported
  let mut items' : Array Syntax := #[]
  for item in items do
    if let some s := item[0].isStrLit? then
      for atom in splitMolecule s do
        items' := items'.push <| ← withRef item
          `(Mathlib.Notation3.notation3Item| $(quote atom):str)
    else
      items' := items'.push item
  return s.setArg 8 (mkNullNode items')

attribute [macro Mathlib.Notation3.notation3] expandNotation3Molecules
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

section RCases
open RCases

partial
def Lean.Elab.Tactic.RCases.RCasesPatt.collect_names : RCasesPatt → List Name
  | one _ `_ | one _ `rfl  => []
  | one _ n => [n]
  | paren _ p | typed _ p _ => p.collect_names
  | alts _ l | tuple _ l  => (l.map collect_names).flatten
  | _           => []

def checkRCasesPattName (p : RCasesPatt) : TacticM Unit :=
  for n in p.collect_names do
    checkName n
end RCases

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

section canonical_info
/- Propagate source information utils by Wojciech Nawrocki. -/

def Lean.SourceInfo.mkCanonical : SourceInfo → SourceInfo
  | .synthetic s e _ => .synthetic s e true
  | si => si

partial def Lean.Syntax.mkInfoCanonical : Syntax → Syntax
  | .missing => .missing
  | .node i k a => .node i.mkCanonical k (a.map mkInfoCanonical)
  | .atom i v => .atom i.mkCanonical v
  | .ident i r v p => .ident i.mkCanonical r v p

def Lean.TSyntax.mkInfoCanonical {k} : TSyntax k → TSyntax k :=
  (⟨·.raw.mkInfoCanonical⟩)
end canonical_info

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
| _ => pure ⟨.missing⟩

def maybeTypedIdentToExplicitBinder : TSyntax `maybeTypedIdent → MetaM (TSyntax `Lean.explicitBinders)
| `(maybeTypedIdent| ($x:ident : $type:term)) => `(explicitBinders|($x:ident : $type))
| `(maybeTypedIdent| $x:ident : $type:term) => `(explicitBinders|($x:ident : $type))
| `(maybeTypedIdent| $x:ident) => `(explicitBinders|$x:ident)
| _ => pure ⟨.missing⟩

def maybeTypedIdentToRcasesPat : TSyntax `maybeTypedIdent → MetaM (TSyntax `Lean.Parser.Tactic.rcasesPatLo)
| `(maybeTypedIdent| ($x:ident : $_type:term)) => `(rcasesPatLo|$x)
| `(maybeTypedIdent| $x:ident : $_type:term) => `(rcasesPatLo|$x)
| `(maybeTypedIdent| $x:ident) => `(rcasesPatLo|$x)
| _ => pure ⟨.missing⟩

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
| _ => pure ⟨.missing⟩

def namedTypeToTypeTerm : TSyntax `namedType → MetaM Term
| `(namedType| ($_x:ident : $type:term)) => `($type)
| `(namedType| $_x:ident : $type:term) => `($type)
| _ => pure ⟨.missing⟩

def namedTypeToRcasesPat : TSyntax `namedType → MetaM (TSyntax `Lean.Parser.Tactic.rcasesPatLo)
| `(namedType| ($x:ident : $_type:term)) => `(rcasesPatLo|$x)
| `(namedType| $x:ident : $_type:term) => `(rcasesPatLo|$x)
| _ => pure ⟨.missing⟩

def NamedType.RCasesPatt : NamedType → RCasesPatt
| (n, pe) => RCasesPatt.typed Syntax.missing (RCasesPatt.one Syntax.missing  n) pe

def namedTypeListToRCasesPatt : List (TSyntax `namedType) → RCasesPatt
| [] => default -- should not happen
| [x] => (toNamedType x).RCasesPatt
| l => RCasesPatt.tuple Syntax.missing <| l.map (NamedType.RCasesPatt ∘ toNamedType)

def Lean.Name.toTerm (n : Lean.Name) : Term := ⟨mkIdent n⟩

def Except.emoji! : Except Exception Bool → String
    | .ok true => checkEmoji
    | _ => crossEmoji

/-- A version of MVarId.apply that takes a name instead of an Expr and return none instead
of failing when the lemma does not apply. The tactic state is preserved in case of failure. -/
def tryLemma (goal : MVarId) (lem : Name) : TacticM (Option (List MVarId)) := do
  let state ← saveState
  goal.withContext do
  let applyGoals ← try
    goal.apply (← elabTermForApply lem.toTerm)
  catch e =>
    trace[Verbose] "Application failed with message {e.toMessageData}"
    restoreState state
    return none
  return applyGoals

/-- Try to close the given goal using the given named lemmas. Return the success status.
Will preserve state in case of failure. -/
def tryLemmas (goal : MVarId) (lemmas : Array Name) : TacticM Bool := do
  let state ← saveState
  for lem in lemmas do
    if (← withTraceNode `Verbose (do return m!"{·.emoji!} Will try {lem}") do
    if let some goals ← tryLemma goal lem then
      try
        for goal in goals do
          if ← goal.isAssigned then
            continue
          trace[Verbose] "Will try assumption to prove side goal {← goal.getType}"
          goal.assumption
        return true
      catch
      | _ =>
        state.restore
        return false
    else
      state.restore
      return false) then return true
  return false

def tryApply (goal : MVarId) (e : Expr) : MetaM Bool := goal.withContext do
  withTraceNode `Verbose (do return s!"{·.emoji!} Will try to apply expression {← ppExpr e}") do
  let state ← saveState
  try
    let newGoals ← goal.apply e
    trace[Verbose] "New goals {newGoals}"
    if newGoals matches [] then
      trace[Verbose] "Successful application"
      return true
  catch _ => pure ()
  state.restore
  return false

def tryRefl : TacticM Bool := withMainContext <| focus do
  withTraceNode `Verbose (do return s!"{·.emoji!} Will try reflexivity") do
  let state ← saveState
  try
    evalTactic (← `(tactic|rfl))
    return true
  catch _ => pure ()
  state.restore
  return false


/-! ## The strongAssumption tactic and term elaborator -/

register_endpoint doesntFollow (tgt : MessageData) : CoreM MessageData

/-- A version of the `assumption` tactic that also try `apply h` for each local assumption `h`,
as well as `And.left h`, `And.right h`, `Eq.symm h` or `Iff.symm h` if appropriate. -/
def assumption' : TacticM Unit := do
  withTraceNode `Verbose (do return m!"{·.emoji} Will try to apply each local assumption") do
  let goal ← getMainGoal
  withAssignableSyntheticOpaque do
  let target ← goal.getType
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if (← withTraceNode `Verbose (do return m!"{·.emoji!} Will try {ldecl.userName}") do
    if ← tryApply goal ldecl.toExpr then return true
    if ldecl.type.isAppOf ``And then
      if ← tryApply goal (← mkAppM ``And.left #[ldecl.toExpr]) then return true
      if ← tryApply goal (← mkAppM ``And.right #[ldecl.toExpr]) then return true
    if ldecl.type.isAppOf ``Eq then
      if ← tryApply goal (← mkAppM ``Eq.symm #[ldecl.toExpr]) then return true
    if ldecl.type.isAppOf ``Iff then
      if ← tryApply goal (← mkAppM ``Iff.symm #[ldecl.toExpr]) then return true
    return false) then return
  if (← tryRefl) then return
  throwTacticEx `byAssumption goal (← doesntFollow (indentExpr target))

def isRelation (e : Expr) : MetaM Bool := do
  return e.isAppOf ``Eq || e.isAppOf ``LE.le || e.isAppOf ``LT.lt ||
         e.isAppOf ``GE.ge|| e.isAppOf ``GT.gt

open Linarith in
def strongAssumption (goal : MVarId) : TacticM Unit := goal.withContext do
  pushGoal goal
  let target ← goal.getType
  focusAndDone do
  withTraceNode `Verbose (do return s!"{·.emoji} Will try the strong assumption tactic to prove {← ppExpr target}") do
  assumption' <|> do
  if ← (withTraceNode `Verbose (do return s!"{·.emoji!} Will now try linarith only") do
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      unless ← isRelation ldecl.type do continue
      trace[Verbose] "Will try to use linarith only [{ldecl.userName}]"
      let state ← saveState
      try
        linarith true [ldecl.toExpr] {preprocessors := defaultPreprocessors} goal
        trace[Verbose] "Success with {ldecl.userName}"
        return true
      catch _ => state.restore
    return false) then return
  if ← (withTraceNode `Verbose (do return s!"{·.emoji!} Will now try linarith only []") do
    let state ← saveState
    try
      linarith true [] {preprocessors := defaultPreprocessors} goal
      trace[Verbose] "Success"
      return true
    catch _ =>
      state.restore
      return false) then return
  if ← (withTraceNode `Verbose (do return s!"{·.emoji!} Will try anonymous fact splitting lemmas") do
    tryLemmas goal (← verboseConfigurationExt.get).anonymousFactSplittingLemmas) then return
  if ← (withTraceNode `Verbose (do return s!"{·.emoji!} Will try anonymous goal splitting lemmas") do
    tryLemmas goal (← verboseConfigurationExt.get).anonymousGoalSplittingLemmas) then return
  trace[Verbose] "strong assumption failed"
  throwTacticEx `strongAssumption (← getMainGoal) (← doesntFollow (indentExpr target))

/-- A version of the assumption tactic that also tries to run `linarith only [x]` for each local declaration `x`. -/
elab "strongAssumption" : tactic => do
  strongAssumption (← getMainGoal)

macro "strongAssumption%" x:term : term => `((by strongAssumption : $x))

register_endpoint couldNotProve (goal : Format) : CoreM String

register_endpoint failedProofUsing (goal : Format) : CoreM String

initialize registerTraceClass `Verbose

register_endpoint cannotContrapose : CoreM String

def Lean.MVarId.check_can_contrapose (goal : MVarId) : MetaM Unit := do
  let tgt ← whnf (← goal.getType)
  unless tgt.isForall do
    throwError ← cannotContrapose
  let p := tgt.bindingDomain!
  let q := tgt.bindingBody!
  unless (← inferType p).isProp && (← inferType q).isProp do
    throwError ← cannotContrapose

namespace Lean.Meta
private def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ "\n"

/-- Variant of `Lean.Meta.ppGoal` filtering the local declaration using the given condition.
Only one line differs, everything else is copy-pasted.
-/
def ppGoalFiltered (mvarId : MVarId) (cond : LocalDecl → Bool) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
    let indent         := 2 -- Use option
    let showLetValues  := pp.showLetValues.get (← getOptions)
    let ppAuxDecls     := pp.auxDecls.get (← getOptions)
    let ppImplDetailHyps := pp.implementationDetailHyps.get (← getOptions)
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    withLCtx lctx mvarDecl.localInstances do
      -- The following two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format := do
        if ids.isEmpty then
          return fmt
        else
          let fmt := addLine fmt
          match type? with
          | none      => return fmt
          | some type =>
            let typeFmt ← ppExpr type
            return fmt ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Format) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Format) := do
        match localDecl with
        | .cdecl _ _ varName type _ _ =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            return (varName :: varNames, some type, fmt)
          else do
            let fmt ← pushPending varNames prevType? fmt
            return ([varName], some type, fmt)
        | .ldecl _ _ varName type val _ _ => do
          let varName := varName.simpMacroScopes
          let fmt ← pushPending varNames prevType? fmt
          let fmt  := addLine fmt
          let type ← instantiateMVars type
          let typeFmt ← ppExpr type
          let mut fmtElem  := format varName ++ " : " ++ typeFmt
          if showLetValues then
            let val ← instantiateMVars val
            let valFmt ← ppExpr val
            fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
          let fmt := fmt ++ fmtElem.group
          return ([], none, fmt)
      let (varNames, type?, fmt) ← lctx.foldlM (init := ([], none, Format.nil)) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
         if (!ppAuxDecls && localDecl.isAuxDecl || !ppImplDetailHyps && localDecl.isImplementationDetail) || !cond localDecl then
return (varNames, prevType?, fmt)
         else
           ppVars varNames prevType? fmt localDecl
      let fmt ← pushPending varNames type? fmt
      let fmt := addLine fmt
      let typeFmt ← ppExpr (← instantiateMVars mvarDecl.type)
      let fmt := fmt ++ getGoalPrefix mvarDecl ++ Format.nest indent typeFmt
      match mvarDecl.userName with
      | Name.anonymous => return fmt
      | name           => return "case " ++ format name.eraseMacroScopes ++ "\n" ++ fmt

section fixed_push_neg
/- In this section we fix an oversight in the `push_neg.use_distrib` option.
Because bounded existential quantifiers are defined using `And` in Lean 4,
this option does the wrong thing to negate them. We fix this by using ad hoc simp
lemmas after using `push_neg`. -/

lemma push_neg_fix₁ {α : Type*} [LinearOrder α] (P : α → Prop) (a : α) :
    (∀ x, a < x ∨ P x) ↔ ∀ x ≤ a, P x := by
  simp_rw [← not_le (b := a), imp_iff_not_or]

lemma push_neg_fix₂ {α : Type*} [LinearOrder α] (P : Prop) (a : α) :
    (∀ x, a ≤ x ∨ P) ↔ ∀ x < a, P := by
  simp_rw [← not_lt (b := a), imp_iff_not_or]

lemma push_neg_fix₃ {α : Type*} [LinearOrder α] (P : α → Prop) (a : α) :
(∀ x : α, x < a ∨ P x) ↔ ∀ (x : α), x ≥ a → P x := by
  simp_rw [← not_lt (b := a), imp_iff_not_or, not_not]

lemma push_neg_fix₄ {α : Type*} [LinearOrder α] (P : α → Prop) (a : α) :
    (∀ x : α, x ≤ a ∨ P x) ↔ ∀ (x : α), x > a → P x := by
  simp_rw [← not_le (b := a), imp_iff_not_or, not_not]

lemma push_neg_fix₅ {α : Type*} (s : Set α) (P : α → Prop) :
    (∀ x : α, x ∉ s ∨ P x) ↔ ∀ (x : α), x ∈ s → P x := by
  simp_rw [imp_iff_not_or]

lemma push_neg_fix₆ {α : Type*} (s : Set α) (P : α → Prop) :
    (∀ x : α, x ∈ s ∨ P x) ↔ ∀ (x : α), x ∉ s → P x := by
  simp_rw [imp_iff_not_or, not_not]

open Mathlib.Tactic.PushNeg in
elab "fixed_push_neg" loc:(location)? : tactic => do
  evalTactic (←
    `(tactic|(
       set_option push_neg.use_distrib true in
       try push_neg $[$loc]?
       try
         simp only [push_neg_extra] $[$loc]?
       try
         simp only [push_neg_fix₁, push_neg_fix₂, push_neg_fix₃, push_neg_fix₄, push_neg_fix₅, push_neg_fix₆] $[$loc]?)))

set_option linter.unusedVariables false in
example (h : ¬ (∃ x > 4, 0 < x)) : True := by
  fixed_push_neg at h
  guard_hyp h : ∀ x > 4, x ≤ 0
  trivial

set_option linter.unusedVariables false in
example (h : ¬ (∃ x ∈ (Set.univ : Set ℕ), 0 < x)) : True := by
  fixed_push_neg at h
  guard_hyp h : ∀ x ∈ (Set.univ : Set ℕ), x ≤ 0
  trivial

example : ¬ (∃ x > 4, 0 < x) ↔ ∀ x > 4, x ≤ 0 := by
  fixed_push_neg

@[local push_neg_extra] private axiom not_even (x : ℕ) : (¬ Even x) ↔ Odd x

example (h : ¬ Even 3) : Odd 3 := by
  fixed_push_neg at h
  exact h

end fixed_push_neg

end Lean.Meta

/-- Try to reduce the current goal to the given statement using `push_neg`. -/
def sufficesPushNeg (goal : MVarId) (fVar : FVarId) : TacticM Unit :=
  withTraceNode `Verbose (do return s!"{·.emoji} Will try push_neg") do
  goal.withContext do
  let state ← saveState
  let fVarName ← fVar.getUserName
  let fVarType ← instantiateMVars (← fVar.getType)
  let tgt ← instantiateMVars (← goal.getType)
  let origGoalConsts := tgt.getUsedConstants
  let announcedGoalConsts := fVarType.getUsedConstants
  let unfoldedNames := (← verboseConfigurationExt.get).unfoldableDefs.filter
    (fun n ↦ origGoalConsts.contains n && !announcedGoalConsts.contains n)
  if !unfoldedNames.isEmpty then trace[Verbose] "Will unfold names: {unfoldedNames}"
  let unfoldedGoal ← liftM <| unfoldedNames.foldlM Meta.unfoldTarget goal
  replaceMainGoal [unfoldedGoal]
  trace[Verbose] "Will call push_neg on goal: {← ppExpr (← unfoldedGoal.getType)}"
  -- Now push_neg in both the unfolded goal and the announced goal and see if we
  -- get to the same place. This way we allow announcing a partially pushed goal.
  evalTactic (← `(tactic| try fixed_push_neg))
  withMainContext do
  trace[Verbose] "Will call push_neg on assumption: {← ppExpr fVarType}"
  evalTactic (← `(tactic| try fixed_push_neg at $(mkIdent fVarName):ident))
  let goalAfter ← getMainGoal
  goalAfter.withContext do
  trace[Verbose] "Goal after pushing everywhere is\n{← ppGoal goalAfter }"
  let decl ← getLocalDeclFromUserName fVarName
  if ← isDefEq decl.type (← goalAfter.getType) then
    closeMainGoal `push_neg decl.toExpr false
  else
    state.restore
    failure
