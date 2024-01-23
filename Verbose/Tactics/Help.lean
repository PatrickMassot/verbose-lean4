import Verbose.Tactics.Common
import Verbose.Tactics.Notations
import Verbose.Tactics.We

/-! # Infrastructure for the help tactic

This file provides foundations for the help tactic. Unfortunately there remains of lot of code that
is duplicated among the language folders since the help tactic really mixes analyzing expressions and
building tactic syntax.

The whole point of this file is to define a custom version of `Lean.Expr` called `MyExpr`.
`Lean.Expr` is the type of abstract syntax tree representing Lean expression. It is an inductive
type whose main constructors are `.lam` for lambda abstractions, `.app` for function applications
and `.forallE` for dependent function types. The issue with those constructor for our purposes
is that bounded quantifiers are not first-class citizens (`∀ ε > 0, P ε` is encoded as
`∀ ε, ε > 0 → P ε`) and most logical operator are simply not constructor at all.

In order to (try to) have nice pattern matching, `MyExpr` has a lot more constructors including
bounded quantifiers (bother universal and existential) as well as conjunction, disjunction,
equivalence etc. The main function of this file is `Verbose.parse` which turns a
`Lean.Expr` into a `MyExpr`.

This file also has some infrastructure to gradually build the help message while analyzing the
goal or assumptions. Each help suggestion has a tactic syntax explanation which can
be preceded by some comments. The suggestion monad helps accumulating this content.

At the end of the file are more random pieces of helpers, including function that help
building assumption names involving relations (order or set membership).
-/

open Lean Meta Elab Tactic

/-! ## The `MyExpr` inductive type and its relations to `Lean.Expr`. -/

def Lean.Expr.relSymb : Expr → Option String
| .const ``LT.lt _ => pure " < "
| .const ``LE.le _ => pure " ≤ "
| .const ``GT.gt _ => pure " > "
| .const ``GE.ge _ => pure " ≥ "
| .const ``Membership.mem _ => pure " ∈ "
| _ => none


partial def Lean.Expr.relInfo? : Expr → MetaM (Option (String × Expr × Expr))
| .mvar m => do Lean.Expr.relInfo? (← m.getType'')
| e@(_) =>  if e.getAppNumArgs < 2 then
    return none
  else
    return some (← relSymb e.getAppFn, e.appFn!.appArg!, e.appArg!)

namespace Verbose
open Lean

inductive MyExpr
| forall_rel (orig : Expr) (var_Name : Name) (typ : Expr) (rel : String) (rel_rhs : Expr) (propo : MyExpr) : MyExpr
| forall_simple (orig : Expr) (var_Name : Name) (typ : Expr) (propo : MyExpr) : MyExpr
| exist_rel (orig : Expr) (var_Name : Name) (typ : Expr) (rel : String) (rel_rhs : Expr) (propo : MyExpr) : MyExpr
| exist_simple (orig : Expr) (var_Name : Name) (typ : Expr) (propo : MyExpr) : MyExpr
| conjunction (orig : Expr) (propo propo' : MyExpr) : MyExpr
| disjunction (orig : Expr) (propo propo' : MyExpr) : MyExpr
| impl (orig : Expr) (le re : Expr) (lhs : MyExpr) (rhs : MyExpr) : MyExpr
| iff (orig : Expr) (le re : Expr) (lhs rhs : MyExpr) : MyExpr
| equal (orig : Expr) (le re : Expr) : MyExpr
| ineq (orig : Expr) (le : Expr) (symb : String) (re : Expr) : MyExpr
| mem (orig : Expr) (elem : Expr) (set : Expr) : MyExpr
| prop (e : Expr) : MyExpr
| data (e : Expr) : MyExpr
deriving Repr, Inhabited

/-- Convert a `MyExpr` to a string in `MetaM`.
This is only for debugging purposes and not used in actual code. -/
def MyExpr.toStr : MyExpr → MetaM String
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
    let p ← MyExpr.toStr propo
    let p' ← MyExpr.toStr propo'
    pure s!"{p} ∧ {p'}"
| .disjunction _orig propo propo' => do
    let p ← MyExpr.toStr propo
    let p' ← MyExpr.toStr propo'
    pure s!"{p} ∨ {p'}"
| .impl _orig _le _re lhs rhs => do
  let l ← MyExpr.toStr lhs
  let r ← MyExpr.toStr rhs
  pure s!"{l} → {r}"
| .iff _orig _le _re lhs rhs => do
  let l ← MyExpr.toStr lhs
  let r ← MyExpr.toStr rhs
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
| .prop e => do return toString (← ppExpr e)
| .data e => do return toString (← ppExpr e)

def MyExpr.toExpr : MyExpr → Expr
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
| .prop e .. => e
| .data e .. => e


def MyExpr.delab {n : Type → Type} [MonadLiftT MetaM n] [Monad n] (e : MyExpr) : n Term :=
  PrettyPrinter.delab e.toExpr

partial def parse {α : Type}
    {n : Type → Type} [MonadControlT MetaM n] [MonadLiftT MetaM n] [Monad n]
    [Inhabited (n α)]
    (e : Expr) (ret : MyExpr → n α) : n α := do
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
            ret <| MyExpr.forall_rel e n t symb re new
          else
            ret <| MyExpr.forall_simple e n t b'
        | _ => do
          ret <| MyExpr.forall_simple e n t b'
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
    | _ => simple e
  | e => simple e
  where simple e := do
    if (← liftM (do instantiateMVars (← inferType e))).isProp then
      ret <| .prop e
    else
      ret <| .data e

/-
elab "test" x:term : tactic => withMainContext do
  let e ← Elab.Tactic.elabTerm x none
  parse e fun p => do
    logInfo m!"Parse output: {← p.toStr}"
  --  logInfo m!"Parse output: {repr p}"

elab "exp" x:ident: tactic => withMainContext do
  let e ← Meta.getLocalDeclFromUserName x.getId
  logInfo m!"{repr e.value}"


example (P : ℕ → Prop) (Q R : Prop) (s : Set ℕ): True := by
  test ∃ n > 0, P n
  test ∃ n, P n
  test ∀ n, P n
  test ∀ n > 0, P n
  test ∀ n, n+1 > 0 → P n
  test Q ∧ R
  test 0 < 3
  test 0 ∈ s
  test Q → R
  trivial

example (Q R : ℕ → Prop) (P : ℕ → ℕ → Prop) : True := by
  let x := 0
  exp x
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
  trivial -/

/-! # The suggestion monad -/

section Suggestions
open  Std.Tactic.TryThis

inductive SuggestionItem
| comment (content : String)
| tactic (content : String)

instance : ToString SuggestionItem where
  toString | .comment s => s | .tactic s => s

structure SuggestionM.State where
  suggestions : Array Suggestion
  message : Option String := none
  currentPre : Option String := none
  currentTactic : Option (TSyntax `tactic) := none
  currentPost : Option String := none
  deriving Inhabited

abbrev SuggestionM := StateRefT SuggestionM.State MetaM

def flush : SuggestionM Unit := do
  let s ← get
  if let some tac := s.currentTactic then
    set {suggestions := s.suggestions.push {
          preInfo? := s.currentPre
          suggestion := tac
          postInfo? := s.currentPost
         } : SuggestionM.State}
  else
    set {suggestions := s.suggestions
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
    set {s with currentPost := s.currentPost.push' content}
  else
    set {s with currentPre := s.currentPre.push content}

def pushTactic (tac : TSyntax `tactic)  : SuggestionM Unit := do
  let s ← get
  if s.currentTactic.isSome then
    throwError "There is already a tactic for this suggestion. You may need to call `flush` first."
  set {s with currentTactic := some tac, currentPre := match s.currentPre with | some c => some s!"{c}\n" | none => none}

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
