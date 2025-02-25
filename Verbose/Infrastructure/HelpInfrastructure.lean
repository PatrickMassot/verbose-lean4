import Mathlib.Tactic.Linarith
import Verbose.Infrastructure.Multilingual
import Verbose.Infrastructure.Extension

/-! # Infrastructure for the help tactic

This file provides foundations for the help tactic.

The first main point of this file is to define a custom version of `Lean.Expr` called `VExpr`.
`Lean.Expr` is the type of abstract syntax tree representing Lean expression. It is an inductive
type whose main constructors are `.lam` for lambda abstractions, `.app` for function applications
and `.forallE` for dependent function types. The issue with those constructor for our purposes
is that bounded quantifiers are not first-class citizens (`∀ ε > 0, P ε` is encoded as
`∀ ε, ε > 0 → P ε`) and most logical operator are simply not constructor at all.

In order to (try to) have nice pattern matching, `VExpr` has a lot more constructors including
bounded quantifiers (bother universal and existential) as well as conjunction, disjunction,
equivalence etc. The main function of this file is `Verbose.parse` which turns a
`Lean.Expr` into a `VExpr`.

This file also has some infrastructure to gradually build the help message while analyzing the
goal or assumptions. Each help suggestion has a tactic syntax explanation which can
be preceded by some comments. The suggestion monad `SuggestionM` helps accumulating this content.

At the end of the file are more random pieces of helpers, including function that help
building assumption names involving relations (order or set membership).

It also defines an attribute `unfoldable_def` that can be used to mark definitions whose
unfolding will be suggested by the help tactic and the widget.
-/

open Lean Meta Elab Tactic Term Verbose

/-! ## The `VExpr` inductive type and its relations to `Lean.Expr`. -/

def Lean.Expr.relSymb : Expr → Option String
| .const ``LT.lt _ => pure " < "
| .const ``LE.le _ => pure " ≤ "
| .const ``GT.gt _ => pure " > "
| .const ``GE.ge _ => pure " ≥ "
| .const ``Membership.mem _ => pure " ∈ "
| .const ``HasSubset.Subset _ => pure " ⊆ "
| _ => none

/-- Given an expression which is either describing an inequality or subset or membership,
return a string decribing the relation and the LHS and RHS. -/
partial def Lean.Expr.relInfo? : Expr → MetaM (Option (String × Expr × Expr))
| .mvar m => do Lean.Expr.relInfo? (← m.getType'')
| e@(_) =>  if e.getAppNumArgs < 2 then
    return none
  else
    return match relSymb e.getAppFn with
           | some " ∈ " => some (" ∈ ", e.appArg!, e.appFn!.appArg!)
           | some s => some (s , e.appFn!.appArg!, e.appArg!)
           | none => none

/-- For testing purposes -/
elab "#relInfo" t:term: command =>
  Command.runTermElabM fun _ ↦ do
  let t ← Term.elabTerm t none
  let t ← instantiateMVars t
  let Option.some x ← t.relInfo? | failure
  let (rel, l, r) := x
  logInfo m!"Expression: {t}:\n{← ppExpr l} {rel} {← ppExpr r}"

variable (x : ℕ) (A : Set ℕ)

/--
info: Expression: x > 0:
x  >  0
-/
#guard_msgs in
#relInfo x > 0

/--
info: Expression: x ∈ A:
x  ∈  A
-/
#guard_msgs in
#relInfo x ∈ A

namespace Verbose
open Lean

inductive VExpr
| forall_rel (orig : Expr) (var_Name : Name) (typ : Expr) (rel : String) (rel_rhs : Expr) (propo : VExpr) : VExpr
| forall_simple (orig : Expr) (var_Name : Name) (typ : Expr) (propo : VExpr) : VExpr
| exist_rel (orig : Expr) (var_Name : Name) (typ : Expr) (rel : String) (rel_rhs : Expr) (propo : VExpr) : VExpr
| exist_simple (orig : Expr) (var_Name : Name) (typ : Expr) (propo : VExpr) : VExpr
| conjunction (orig : Expr) (propo propo' : VExpr) : VExpr
| disjunction (orig : Expr) (propo propo' : VExpr) : VExpr
| impl (orig : Expr) (le re : Expr) (lhs : VExpr) (rhs : VExpr) : VExpr
| iff (orig : Expr) (le re : Expr) (lhs rhs : VExpr) : VExpr
| equal (orig : Expr) (le re : Expr) : VExpr
| ineq (orig : Expr) (le : Expr) (symb : String) (re : Expr) : VExpr
| mem (orig : Expr) (elem : Expr) (set : Expr) : VExpr
| subset (orig : Expr) (lhs rhs : Expr) : VExpr
| prop (e : Expr) : VExpr
| data (e : Expr) : VExpr
deriving Repr, Inhabited

/-- Convert a `VExpr` to a string in `MetaM`.
This is only for debugging purposes and not used in actual code. -/
def VExpr.toStr : VExpr → MetaM String
| .forall_rel _orig var_name _typ rel rel_rhs propo => do
    let rhs := toString (← ppExpr rel_rhs)
    let p ← propo.toStr
    pure s!"∀ {var_name}{rel}{rhs}, {p}"
| .forall_simple _orig var_name _typ propo => do
    let p ← propo.toStr
    pure s!"∀ {var_name.toString}, {p}"
| .exist_rel _orig var_name _typ rel rel_rhs propo => do
    let rhs := toString (← ppExpr rel_rhs)
    let p ← propo.toStr
    pure s!"∃ {var_name}{rel}{rhs}, {p}"
| .exist_simple _orig var_name _typ propo => do
    let p ← propo.toStr
    pure s!"∃ {var_name.toString}, {p}"
| .conjunction _orig propo propo' => do
    let p ← VExpr.toStr propo
    let p' ← VExpr.toStr propo'
    pure s!"{p} ∧ {p'}"
| .disjunction _orig propo propo' => do
    let p ← VExpr.toStr propo
    let p' ← VExpr.toStr propo'
    pure s!"{p} ∨ {p'}"
| .impl _orig _le _re lhs rhs => do
  let l ← VExpr.toStr lhs
  let r ← VExpr.toStr rhs
  pure s!"{l} → {r}"
| .iff _orig _le _re lhs rhs => do
  let l ← VExpr.toStr lhs
  let r ← VExpr.toStr rhs
  pure s!"{l} ↔ {r}"
| .equal _orig le re => do
  let l := toString (← ppExpr le)
  let r := toString (← ppExpr re)
  pure s!"{l} = {r}"
| .ineq _orig le symb re => do
  let l := toString (← ppExpr le)
  let r := toString (← ppExpr re)
  pure s!"{l}{symb}{r}"
| .mem _orig elem set => do
  let l := toString (← ppExpr elem)
  let r := toString (← ppExpr set)
  pure s!"{l} ∈ {r}"
| .subset _orig lhs rhs => do
  let l := toString (← ppExpr lhs)
  let r := toString (← ppExpr rhs)
  pure s!"{l} ⊆ {r}"
| .prop e => do return toString (← ppExpr e)
| .data e => do return toString (← ppExpr e)

def VExpr.toExpr : VExpr → Expr
| .forall_rel e .. => e
| .forall_simple e .. => e
| .exist_rel e .. => e
| .exist_simple e .. => e
| .conjunction e .. => e
| .disjunction e .. => e
| .impl e .. => e
| .iff e .. => e
| .equal e .. => e
| .ineq e .. => e
| .mem e .. => e
| .subset e .. => e
| .prop e .. => e
| .data e .. => e


def VExpr.delab {n : Type → Type} [MonadLiftT MetaM n] [Monad n] (e : VExpr) : n Term :=
  PrettyPrinter.delab e.toExpr

partial def parse {α : Type}
    {n : Type → Type} [MonadControlT MetaM n] [MonadLiftT MetaM n] [Monad n]
    [Inhabited (n α)]
    (e : Expr) (ret : VExpr → n α) : n α := do
  have : n α := ret default
  match e with
  | Expr.forallE n t b bi =>
    if e.isArrow then do
      parse t fun left ↦ parse b fun right ↦ ret <| .impl e t b left right
    else
      withLocalDecl n bi t fun x ↦ parse (b.instantiate1 x) fun b' ↦
        match b' with
        | .impl _ _ _ (.ineq _ le symb re) new => do
          if (← isDefEq le x) then
            ret <| VExpr.forall_rel e n t symb re new
          else
            ret <| VExpr.forall_simple e n t b'
        | .impl _ _ _ (.mem _ le re) new => do
          if (← isDefEq le x) then
            ret <| VExpr.forall_rel e n t " ∈ " re new
          else
            ret <| VExpr.forall_simple e n t b'
        | .impl _ _ _ (.subset _ le re) new => do
          if (← isDefEq le x) then
            ret <| VExpr.forall_rel e n t " ⊆ " re new
          else
            ret <| VExpr.forall_simple e n t b'
        | _ => do
          ret <| VExpr.forall_simple e n t b'
  | e@(.app ..) => do
    match e.getAppFn with
    | .const `Exists .. => do
      let binding := e.getAppArgs'[1]!
      let varName := binding.bindingName!
      let varType := binding.bindingDomain!
      withLocalDecl varName binding.binderInfo varType fun x => do
        let body := binding.bindingBody!.instantiate1 x
        if body.isAppOf `And then
          if let some (rel, _, rhs) ← body.getAppArgs[0]!.relInfo? then
            -- **TODO**: also check the lhs is the expected one
            return ← parse body.getAppArgs'[1]! fun b' ↦ ret <| .exist_rel e varName varType rel rhs b'
        return ← parse body fun b' ↦ ret <| .exist_simple e varName varType b'
    | .const `And .. =>
      parse e.getAppArgs[0]! fun left ↦ parse e.getAppArgs[1]! fun right ↦ ret <| .conjunction e left right
    | .const `Or .. =>
      parse e.getAppArgs[0]! fun left ↦ parse e.getAppArgs[1]! fun right ↦ ret <| .disjunction e left right
    | .const `Iff .. =>
      parse e.getAppArgs[0]! fun left ↦ parse e.getAppArgs[1]! fun right ↦ ret <| .iff e e.getAppArgs[0]! e.getAppArgs[1]! left right
    | .const `Eq .. => ret <| .equal e e.getAppArgs[1]! e.getAppArgs[2]!
    | .const `LE.le _ | .const `LT.lt _ | .const `GE.ge _ | .const `GT.gt _ => do
      let some (rel, lhs, rhs) ← e.relInfo? | unreachable!
      ret <| .ineq e lhs rel rhs
    | .const `Membership.mem _ => do
      let some (_, lhs, rhs) ← e.relInfo? | unreachable!
      ret <| .mem e lhs rhs
    | .const `HasSubset.Subset _ => do
      let some (_, lhs, rhs) ← e.relInfo? | unreachable!
      ret <| .subset e lhs rhs
    | _ => simple e
  | e => simple e
  where simple e := do
    if (← liftM (do instantiateMVars (← inferType e))).isProp then
      ret <| .prop e
    else
      ret <| .data e


elab "test " x:term : tactic => withMainContext do
  let e ← Elab.Tactic.elabTerm x none
  parse e fun p => do
    logInfo m!"Parse output: {← p.toStr}"
    -- logInfo m!"Parse output: {repr p}"

elab "exp " x:ident: tactic => withMainContext do
  let e ← Meta.getLocalDeclFromUserName x.getId
  logInfo m!"{repr e.value}"


/--
info: Parse output: ∃ n > 0, P n
---
info: Parse output: ∃ n, P n
---
info: Parse output: ∀ n, P n
---
info: Parse output: ∀ n > 0, P n
---
info: Parse output: ∀ n, n + 1 > 0 → P n
---
info: Parse output: Q ∧ R
---
info: Parse output: 0 < 3
---
info: Parse output: 0 ∈ s
---
info: Parse output: Q → R
---
info: Parse output: s ⊆ t
---
info: Parse output: ∀ n ∈ s, P n
---
info: Parse output: ∀ u ⊆ s, True
---
info: Parse output: t ⊆ s
---
info: Parse output: ℕ → ℕ → 1 > 2 → True
---
info: Parse output: ∀ x, ∀ y, x > y → True
---
info: Parse output: ∀ x, ∀ y > x, True
---
info: Parse output: ∀ x, ∀ y, x ≤ y → True
-/
#guard_msgs in
set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
example (P : ℕ → Prop) (Q R : Prop) (s t : Set ℕ): True := by
  test ∃ n > 0, P n
  test ∃ n, P n
  test ∀ n, P n
  test ∀ n > 0, P n
  test ∀ n, n+1 > 0 → P n
  test Q ∧ R
  test 0 < 3
  test 0 ∈ s
  test Q → R
  test s ⊆ t
  test ∀ n ∈ s, P n
  test ∀ u ⊆ s, True
  test t ⊆ s
  test ∀ (x y : Nat), 1 > 2 → True
  test ∀ (x y : Nat), x > y → True
  test ∀ (x y : Nat), y > x → True
  test ∀ (x y : Nat), x ≤ y → True
  trivial

/--
info: Parse output: R 1 → Q 2
---
info: Parse output: ∀ l, l - 3 = 0 → P l 0
---
info: Parse output: ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k
---
info: Parse output: ∃ n ≥ 5, Q n
---
info: Parse output: ∀ k ≥ 2, ∃ n ≥ 3, P n k
---
info: Parse output: ∃ n, Q n
---
info: Parse output: ∀ k, ∃ n, P n k
---
info: Parse output: ∀ k ≥ 2, ∃ n, P n k
---
info: Parse output: ∀ k, Q k → ∀ l, R l
---
info: Parse output: ∀ k, Q k ↔ ∀ l, R l
---
info: Parse output: ∀ k, 1 ≤ k → Q k
-/
#guard_msgs in
set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
example (Q R : ℕ → Prop) (P : ℕ → ℕ → Prop) : True := by
  test R 1 → Q 2
  test ∀ l, l - 3 = 0 → P l 0
  test ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k
  test ∃ n ≥ 5, Q n
  test ∀ k ≥ 2, ∃ n ≥ 3, P n k
  test ∃ n, Q n
  test ∀ k, ∃ n, P n k
  test ∀ k ≥ 2, ∃ n, P n k
  test (∀ k : ℕ, Q k) → (∀ l , R l)
  test (∀ k : ℕ, Q k) ↔ (∀ l , R l)
  test ∀ k, 1 ≤ k → Q k
  trivial

/-! # The suggestion monad -/

section Suggestions
open  Lean.Meta.Tactic.TryThis

inductive SuggestionItem
| comment (content : String)
| tactic (content : String)

instance : ToString SuggestionItem where
  toString | .comment s => s | .tactic s => s

structure SuggestionM.State where
  suggestions : Array Suggestion
  flushed := true
  message : Option String := none
  currentPre : Option String := none
  currentTactic : Option (TSyntax `tactic) := none
  currentPost : Option String := none
  deriving Inhabited

abbrev SuggestionM := StateRefT SuggestionM.State MetaM

def flush : SuggestionM Unit := do
  let s ← get
  if !s.flushed then
    if let some tac := s.currentTactic then
      set {
        flushed := true
        suggestions := s.suggestions.push {
          preInfo? := s.currentPre
          suggestion := tac
          postInfo? := s.currentPost
        } : SuggestionM.State}
    else
      set {flushed := true
           suggestions := s.suggestions
           message := s.currentPre : SuggestionM.State}

def _root_.Option.push (new : String) : Option String → Option String
| some s => some s!"{s}\n{new}"
| none => some new

def _root_.Option.push' (new : String) : Option String → Option String
| some s => some s!"{s}\n{new}"
| none => some s!"\n{new}"


def pushComment (content : String) : SuggestionM Unit := do
  let s ← get
  if s.currentTactic.isSome then
    set {s with flushed := false, currentPost := s.currentPost.push' content}
  else
    set {s with flushed := false, currentPre := s.currentPre.push content}

def pushTactic (tac : TSyntax `tactic)  : SuggestionM Unit := do
  let s ← get
  if s.currentTactic.isSome then
    throwError "There is already a tactic for this suggestion. You may need to call `flush` first."
  set {s with flushed := false, currentTactic := some tac, currentPre := match s.currentPre with | some c => some s!"{c}\n" | none => none}

macro "pushTac" quoted:term : term => `(do pushTactic (← $quoted))

syntax:max "pushCom" interpolatedStr(term) : term

macro_rules
  | `(pushCom $interpStr) => do
    let s ← interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
    `(pushComment $s)

def gatherSuggestions {α : Type} (s : SuggestionM α) : MetaM ((Array Suggestion) × Option String) := do
  let s' : SuggestionM Unit := do
    discard s
    flush
  let out := (← s'.run default).2
  return (out.suggestions, out.message)

end Suggestions

/-! ## Help extensions -/

structure HypHelpExt where
  name : Name := by exact decl_name% -- auto fill with the name of the declaration which is tagged.
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit

/-- Read a `help` extension from a declaration of the right type. -/
def mkHypHelpExt (n : Name) : ImportM HypHelpExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck HypHelpExt opts ``HypHelpExt n

/-- Each `help` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev HypHelpEntry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `help` declarations -/
initialize hypHelpExt : PersistentEnvExtension HypHelpEntry (HypHelpEntry × HypHelpExt)
    (List HypHelpEntry × DiscrTree HypHelpExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq HypHelpExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkHypHelpExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

/-- Attribute for identifying `hypHelp` extensions. -/
syntax (name := hypHelp) "hypHelp " term,+ : attr

initialize registerBuiltinAttribute {
  name := `hypHelp
  descr := "adds a hypothesis help extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| hypHelp $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'hypHelp', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'hypHelp', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkHypHelpExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx => do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      setEnv <| hypHelpExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}

/-- Print all hypotheses help providers, even if they are not active, for debugging purposes. -/
elab "#print_hyp_helps" : command => do
  for ext in (hypHelpExt.getState (← getEnv)).1 do
    IO.println ext.2

structure GoalHelpExt where
  name : Name := by exact decl_name% -- auto fill with the name of the declaration which is tagged.
  run (goal : MVarId) (goalMExpr : VExpr) : SuggestionM Unit

/-- Read a `help` extension from a declaration of the right type. -/
def mkGoalHelpExt (n : Name) : ImportM GoalHelpExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck GoalHelpExt opts ``GoalHelpExt n

/-- Each `help` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev GoalHelpEntry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `help` declarations -/
initialize goalHelpExt : PersistentEnvExtension GoalHelpEntry (GoalHelpEntry × GoalHelpExt)
    (List GoalHelpEntry × DiscrTree GoalHelpExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq GoalHelpExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkGoalHelpExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

/-- Attribute for identifying `goalHelp` extensions. -/
syntax (name := goalHelp) "goalHelp " term,+ : attr

initialize registerBuiltinAttribute {
  name := `goalHelp
  descr := "adds a goal help extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| goalHelp $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'goalHelp', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'goalHelp', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkGoalHelpExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx => do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      setEnv <| goalHelpExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}

/-- Print all goal help providers, even if they are not active, for debugging purposes. -/
elab "#print_goal_helps" : command => do
  for ext in (goalHelpExt.getState (← getEnv)).1 do
    IO.println ext.2


protected instance (priority := high) Fun.instNonempty {ι : Sort*} {α : Sort*} [Nonempty α] :
    Nonempty (ι → α) :=
  ⟨fun _ ↦ Classical.arbitrary _⟩


/-! ## Relation symbols utils -/

def mkRelStx (var : Name) (symb : String) (rhs : Expr) : MetaM Term := do
  let i := mkIdent var
  let rhsS ← Lean.PrettyPrinter.delab rhs
  match symb with
  | " ≥ " => `($i ≥ $rhsS)
  | " > " => `($i > $rhsS)
  | " ≤ " => `($i ≤ $rhsS)
  | " < " => `($i < $rhsS)
  | " = " => `($i = $rhsS)
  | " ∈ " => `($i ∈ $rhsS)
  | _ => default

def mkFixDeclIneq (var : Name) (symb : String) (rhs : Expr) : MetaM (TSyntax `fixDecl) := do
  let r ← mkRelStx var symb rhs
  return .mk r

def mkRelStx' (lhs : Expr) (symb : String) (rhs : Expr) : MetaM Term := do
  let lhsS ← Lean.PrettyPrinter.delab lhs
  let rhsS ← Lean.PrettyPrinter.delab rhs
  match symb with
  | " ≥ " => `($lhsS ≥ $rhsS)
  | " > " => `($lhsS > $rhsS)
  | " ≤ " => `($lhsS ≤ $rhsS)
  | " < " => `($lhsS < $rhsS)
  | " = " => `($lhsS = $rhsS)
  | " ∈ " => `($lhsS ∈ $rhsS)
  | _ => default

def symb_to_hyp : String → Expr → String
| " ≥ ", (.app (.app (.app (.const `OfNat.ofNat ..) _) (.lit <| .natVal 0)) _) => "_pos"
| " ≥ ", _ => "_sup"
| " > ", (.app (.app (.app (.const `OfNat.ofNat ..) _) (.lit <| .natVal 0)) _) => "_pos"
| " > ", _ => "_sup"
| " ≤ ", (.app (.app (.app (.const `OfNat.ofNat ..) _) (.lit <| .natVal 0)) _) => "_neg"
| " ≤ ", _ => "_inf"
| " < ", (.app (.app (.app (.const `OfNat.ofNat ..) _) (.lit <| .natVal 0)) _) => "_neg"
| " < ", _ => "_inf"
| " ∈ ", _ => "_dans"
| _, _ => ""

end Verbose

/-! ## Misc help utils -/

def Lean.Expr.closesGoal (e : Expr) (goal : MVarId) : MetaM Bool :=
  withoutModifyingState do isDefEq e (← instantiateMVars (← goal.getType))

def Lean.Expr.linarithClosesGoal (e : Expr) (goal : MVarId) : MetaM Bool :=
  withoutModifyingState do
    try
      Linarith.linarith true [e] {preprocessors := Linarith.defaultPreprocessors} goal
      return true
    catch _ => return false

def withRenamedFVar {n : Type → Type} [MonadControlT MetaM n] [MonadLiftT MetaM n] [Monad n]
    (old new : Name) {α : Type} (x : n α) : n α := do
  withLCtx ((← liftMetaM getLCtx).renameUserName old new) {} x

def Lean.Expr.isAppFnUnfoldable (e : Expr) : CoreM Bool := do
  if e.isApp then
    if let .const name _ := e.getAppFn  then
      let lemmas := (← verboseConfigurationExt.get).unfoldableDefs
      pure <| lemmas.contains name
    else
      pure false
  else
    pure false

def Lean.Expr.memInterPieces? (e : Expr) : Option (Expr × Expr) := do
  if e.isApp then
    if e.getAppFn matches .const `Inter.inter _ then
      let args := e.getAppArgs
      if h : 3 < args.size then
        return (args[2]!, args[3])
  none

def Lean.Expr.memUnionPieces? (e : Expr) : Option (Expr × Expr) := do
  if e.isApp then
    if e.getAppFn matches .const `Union.union _ then
      let args := e.getAppArgs
      if h : 3 < args.size then
        return (args[2]!, args[3])
  none


alias Lean.Name.ident := Lean.mkIdent
alias Lean.Expr.fmt := Lean.PrettyPrinter.ppExpr
alias Lean.Expr.stx := Lean.PrettyPrinter.delab
alias Lean.Syntax.Term.fmt := Lean.PrettyPrinter.ppTerm


/-- If the given expression can be applied to prove the given goal,
without creating meta-variables, then return the instantiated proof,
otherwise return `None`. -/
def Lean.Expr.applyToGoal (e : Expr) (goal : MVarId) : MetaM (Option Expr) :=
  withoutModifyingState do
  let _ ← goal.apply e
  let prf ← instantiateMVars (mkMVar goal)
  return if prf.hasMVar then none else some prf

/-! # Elaborator for `mkAppN f #[...]`

Expands this expression into an expression using just `Expr.app` so that it can be used in patterns.
By Kyle Miller. -/


@[inherit_doc mkAppN]
macro_rules
  | `(mkAppN $f #[$xs,*]) =>
    (xs.getElems.foldlM (fun x e => `(Expr.app $x $e)) f : MacroM Term)
