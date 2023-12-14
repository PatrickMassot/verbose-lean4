import Verbose.Tactics.Common
import Verbose.Tactics.We

-- **FIXME** move out of here and into French
import Verbose.French.All

open Lean Meta Elab Tactic

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

def Lean.Expr.closesGoal (e : Expr) (goal : MVarId) : MetaM Bool :=
  withoutModifyingState do isDefEq e (← goal.getType)

def Lean.Expr.linarithClosesGoal (e : Expr) (goal : MVarId) : MetaM Bool :=
  withoutModifyingState do
    try
      Linarith.linarith true [e] {preprocessors := Linarith.defaultPreprocessors} goal
      return true
    catch _ => return false

def withRenamedFVar {n : Type → Type} [MonadControlT MetaM n] [MonadLiftT MetaM n] [Monad n]
    (old new : Name) {α : Type} (x : n α) : n α := do
  withLCtx ((← liftMetaM getLCtx).renameUserName old new) {} x

def Lean.MVarId.getUnusedUserName {n : Type → Type} [MonadControlT MetaM n] [MonadLiftT MetaM n]
    [Monad n] (goal : MVarId) (suggestion : Name) : n Name := do
  return (← goal.getDecl).lctx.getUnusedUserName suggestion


set_option autoImplicit false

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

inductive SuggestionItem
| comment (content : String)
| tactic (content : String)

instance : ToString SuggestionItem where
  toString | .comment s => s | .tactic s => s

abbrev SuggestionM := StateRefT (Array SuggestionItem) MetaM

def pushComment (content : String) : SuggestionM Unit := do
  set <| (← get).push (.comment content)

def pushTactic (content : String) : SuggestionM Unit := do
  set <| (← get).push (.tactic content)

def gatherSuggestions {α : Type} (s : SuggestionM α) : MetaM (Array SuggestionItem) := do
  return (← s.run #[]).2

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
        | .impl _ _ _ (.ineq _ _ symb re) new => do
           -- TODO: also check the lhs is the expected one
           ret <| MyExpr.forall_rel e n t symb re new
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
            -- TODO: also check the lhs is the expected one
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

-- **FIXME** the fvar part does nothing and this impact uses below.
/-- Une version de `expr.rename_var` qui renomme même les variables libres. -/
def _root_.Lean.Expr.rename (old new : Name) : Expr → Expr
| .forallE n t b bi => .forallE (if n = old then new else n) (t.rename old new) (b.rename old new) bi
| .lam n t b bi => .lam (if n = old then new else n) (t.rename old new) (b.rename old new) bi
| .app t b => .app (t.rename old new) (b.rename old new)
| .fvar x => .fvar x
| e => e

def MyExpr.rename (old new : Name) : MyExpr → MyExpr
| .forall_rel e n typ rel rel_rhs propo => forall_rel e (if n = old then new else n) typ rel rel_rhs $ propo.rename old new
| .forall_simple e n typ propo => forall_simple e (if n = old then new else n) typ $ propo.rename old new
| .exist_rel e n typ rel rel_rhs propo => exist_rel e (if n = old then new else n) typ rel rel_rhs $ propo.rename old new
| .exist_simple e n typ propo => exist_simple e (if n = old then new else n) typ $ propo.rename old new
| .conjunction e propo propo' => conjunction e (propo.rename old new) (propo'.rename old new)
| .disjunction e propo propo' => disjunction e (propo.rename old new) (propo'.rename old new)
| .impl e le re lhs rhs => impl e (le.renameBVar old new) (re.renameBVar old new) (lhs.rename old new) (rhs.rename old new)
| .iff e le re lhs rhs => iff e (le.renameBVar old new) (re.renameBVar old new) (lhs.rename old new) (rhs.rename old new)
| .equal e le re => equal e (le.renameBVar old new) (re.renameBVar old new)
| .ineq e le rel re => ineq e (le.renameBVar old new) rel (re.renameBVar old new)
| .mem e elem set => mem e (elem.renameBVar old new) (set.renameBVar old new)
| .prop e => prop (e.rename old new)
| .data e => data (e.rename old new)


def describe {α :Type} [ToString α] (t : α) : String :=
match toString t with
| "ℝ" => "un nombre réel"
| "ℕ" => "un nombre entier naturel"
| "ℤ" => "un nombre entier relatif"
| t => "une expression de type " ++ t

def describe_pl {α :Type} [ToString α] (t : α) : String :=
match toString t with
| "ℝ" => "des nombres réels"
| "ℕ" => "des nombres entiers naturels"
| "ℤ" => "des nombres entiers relatifs"
| t => "des expressions de type " ++ t

def libre (s: String) : String := s!"Le nom {s} peut être choisi librement parmi les noms disponibles."

def libres (ls : List String) : String :=
"Les noms " ++ String.intercalate ", " ls ++ " peuvent être choisis librement parmi les noms disponibles."

def _root_.Lean.Expr.toMaybeAppliedFR (e : Expr) : MetaM (TSyntax `maybeAppliedFR) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeAppliedFR|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeAppliedFR|$fnS:term appliqué à $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeAppliedFR|$fnS:term appliqué à [$arr:term,*])

macro "pushTac" quoted:term : term => `(do pushTactic <| toString (← Lean.PrettyPrinter.ppTactic (← $quoted)))

syntax:max "pushCom" interpolatedStr(term) : term

macro_rules
  | `(pushCom $interpStr) => do
    let s ← interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
    `(pushComment $s)

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


/-
**FIXME**: All recommendations below should check that suggested names are not already used.
-/
def helpAtHyp (goal : MVarId) (hyp : Name) : SuggestionM Unit :=
  goal.withContext do
  let decl := ← getLocalDeclFromUserName hyp
  let hypId := mkIdent hyp

  parse decl.type fun m ↦ match m with
    | .forall_rel _ var_name typ rel rel_rhs propo => do
        let py ← ppExpr rel_rhs
        let t ← ppExpr typ
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀T := mkIdent nn₀
        let hn₀N ← goal.getUnusedUserName ("h" ++ n₀ : String)
        let hn₀T := mkIdent hn₀N
        withRenamedFVar var_name nn₀ do
        match propo with
        | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let ineqIdent := mkIdent s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
          let ineqS ← mkRelStx var_name' rel' rel_rhs'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}{rel}{py}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $hn₀T] on obtient $(mkIdent var_name'):ident tel que ($ineqIdent : $ineqS) ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t} et {hn₀N} est une démonstration du fait que {nn₀}{rel}{py}."
          pushComment <| libres [s!"{var_name'}", s!"{var_name'}{symb_to_hyp rel' rel_rhs'}", s!"h{var_name'}"]
        | .exist_simple _e' var_name' _typ' propo' => do
          let n' := toString var_name'
          let var_name' := ← goal.getUnusedUserName var_name'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}{rel}{py}, ∃ {n'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $hn₀T] on obtient $(mkIdent var_name'):ident tel que ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t} et h{n₀} est une démonstration du fait que {n₀}{rel}{py}"
          pushComment <| libres [n', s!"h{n'}"]
        | _ => do
          let pS ← propo.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {var_name}{rel}{py}, »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $hn₀T] on obtient ($hn₀T : $pS))
          pushCom "où {n₀} est {describe t} et h{n₀} est une démonstration du fait que {n₀}{rel}{py}"
          pushComment <| libre "h"
    | .forall_simple _ var_name typ propo => do
        let t ← ppExpr typ
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀T := mkIdent nn₀
        let hn₀N ← goal.getUnusedUserName ("h" ++ n₀ : String)
        let hn₀T := mkIdent hn₀N
        withRenamedFVar var_name nn₀ do
        match propo with
        | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let ineqIdent := mkIdent s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
          let ineqS ← mkRelStx var_name' rel' rel_rhs'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à $n₀T on obtient $(mkIdent var_name'):ident tel que ($ineqIdent : $ineqS) ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t}"
          pushComment <| libres [s!"{var_name'}", s!"{var_name'}{symb_to_hyp rel' rel_rhs'}", s!"h{var_name'}"]
        | .exist_simple _e' var_name' _typ' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}, ∃ {var_name'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à $n₀T on obtient $(mkIdent var_name'):ident tel que ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t}"
          pushComment <| libres [toString var_name', s!"h{var_name'}"]
        | .forall_rel _e' var_name' _typ' rel' _rel_rhs' propo' => do
          let n' := toString var_name'
          let var_name'₀ := ← goal.getUnusedUserName (Name.mkSimple ((toString var_name') ++ "₀"))
          withRenamedFVar var_name' var_name'₀ do
          let n'₀T := mkIdent var_name'₀
          let H := ← goal.getUnusedUserName `H
          let HT := mkIdent H
          let h := ← goal.getUnusedUserName `h
          let hT := mkIdent h
          let rel := n ++ rel' ++ n'
          let rel₀ := s!"{nn₀}{rel'}{var_name'₀}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n} {n'}, {rel} → ... "
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $n'₀T, $HT] on obtient ($hT : $p'S))
          pushCom "où {nn₀} et {var_name'₀} sont {describe_pl t} et {H} est une démonstration de {rel₀}"
          pushComment <| libre (toString h)
        | _ => do
          let pS ← propo.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}, »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à $n₀T on obtient ($hn₀T : $pS))
          pushCom "où {n₀} est {describe t}"
          pushComment <| libre "h" ++ ""
          pushCom "Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser {hyp} par"
          pushTac `(tactic|On applique $hypId:ident à $n₀T)
          -- **TODO** cleanup this mess
          let msgM : MetaM (Option <| TSyntax `tactic) := withoutModifyingState do
              (do
              let _ ← goal.apply decl.toExpr
              let prf ← instantiateMVars (mkMVar goal)
              let prfS ← prf.toMaybeAppliedFR
              if !prf.hasMVar then
                some (← `(tactic|On conclut par $prfS))
              else
                none)
            <|>
              pure none
          let msg ← msgM
          if let some msg := msg then
            let but ← ppExpr (← goal.getType)
            pushCom "\nComme le but est {but}, on peut utiliser :"
            pushTac (do return msg)
    | .exist_rel _ var_name _typ rel rel_rhs propo => do
      let y ← ppExpr rel_rhs
      let pS ← propo.delab
      let name ← goal.getUnusedUserName var_name
      let nameS := mkIdent name
      let hS := mkIdent s!"h{name}"
      let ineqName := Name.mkSimple s!"{name}{symb_to_hyp rel rel_rhs}"
      let ineqIdent := mkIdent ineqName
      let ineqS ← mkRelStx name rel rel_rhs
      pushCom "L'hypothèse {hyp} est de la forme « ∃ {var_name}{rel}{y}, ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|Par $hypId:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) ($hS : $pS))
      pushComment <| libres [toString name, s!"{name}{symb_to_hyp rel rel_rhs}", s!"h{name}"]
    | .exist_simple _ var_name _typ propo => do
      let pS ← propo.delab
      let name ← goal.getUnusedUserName var_name
      let nameS := mkIdent name
      let hS := mkIdent s!"h{name}"
      pushCom "L'hypothèse {hyp} est de la forme « ∃ {var_name}, ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|Par $hypId:term on obtient $nameS:ident tel que ($hS : $pS))
      pushComment <| libres [toString name, s!"h{name}"]
    | .conjunction _ propo propo' => do
      let h₁N ← goal.getUnusedUserName `h
      let h₁I := mkIdent h₁N
      let h₂N ← goal.getUnusedUserName `h
      let h₂I := mkIdent h₂N
      let p₁S ← propo.delab
      let p₂S ← propo'.delab
      pushCom "L'hypothèse {hyp} est de la forme « ... et ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|Par $hypId:term on obtient ($h₁I : $p₁S) ($h₂I : $p₂S))
      pushComment <| libres [s!"h₁N", s!"h₂N"]
    | .disjunction _ _propo _propo' => do
      pushCom "L'hypothèse {hyp} est de la forme « ... ou ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|On discute en utilisant $hypId:term)
    | .impl _ _le re lhs rhs => do
      let HN ← goal.getUnusedUserName `H
      let HI := mkIdent HN
      let H'N ← goal.getUnusedUserName `H'
      let H'I := mkIdent H'N
      let l ← lhs.delab
      let lStr ← PrettyPrinter.ppTerm l
      let r ← rhs.delab
      pushCom "L'hypothèse {hyp} est une implication"
      if ← re.closesGoal goal then do
        pushCom "La conclusion de cette implication est le but courant"
        pushCom "On peut donc utiliser cette hypothèse avec :"
        pushTac `(tactic| Par $hypId:term il suffit de montrer $l)
        pushCom "Si vous disposez déjà d'une preuve {HN} de {lStr} alors on peut utiliser :"
        pushTac `(tactic|On conclut par $hypId:term appliqué à $HI)
      else do
        pushCom "La prémisse de cette implication est {lStr}"
        pushCom "Si vous avez une démonstration {HN} de {lStr}"
        pushCom "vous pouvez donc utiliser cette hypothèse avec :"
        pushTac `(tactic|Par $hypId:term appliqué à $HI:term on obtient $H'I:ident : $r:term)
        pushComment <| libre s!"{H'N}"
    | .iff _ _le _re lhs rhs => do
      let l ← lhs.delab
      let lStr ← PrettyPrinter.ppTerm l
      let r ← rhs.delab
      let rStr ← PrettyPrinter.ppTerm r
      let hyp'N ← goal.getUnusedUserName `hyp
      let hyp'I := mkIdent hyp'N
      pushCom "L'hypothèse {hyp} est une équivalence"
      pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {lStr}) par le membre de droite  (c'est à dire {rStr}) dans le but par :"
      pushTac `(tactic|On réécrit via $hypId:term)
      pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
      pushTac `(tactic|On réécrit via ← $hypId)
      pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'N} par"
      pushTac `(tactic|On réécrit via $hypId:term dans $hyp'I:ident)
      pushCom "ou"
      pushTac `(tactic|On réécrit via ← $hypId:term dans $hyp'I:ident)
    | .equal _ le re => do
      let l ← ppExpr le
      let r ← ppExpr re
      let hyp'N ← goal.getUnusedUserName `hyp
      let hyp'I := mkIdent hyp'N
      pushCom "L'hypothèse {hyp} est une égalité"
      if ← decl.toExpr.closesGoal goal then
          pushCom "Cette égalité est exactement ce qu'il faut démontrer"
          pushComment   "On peut l'utiliser avec :"
          pushTac `(tactic|On conclut par $hypId:ident)
      else
        if ← decl.toExpr.linarithClosesGoal goal then
          pushComment <| s!"Le but courant en découle immédiatement"
          pushComment   "On peut l'utiliser avec :"
          pushTac `(tactic|On conclut par $hypId:ident)
        else do
          pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {l}) par le membre de droite  (c'est à dire {r}) dans le but par :"
          pushTac `(tactic|On réécrit via $hypId:ident)
          pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
          pushTac `(tactic|On réécrit via ← $hypId:ident)
          pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'N} par"
          pushTac `(tactic|On réécrit via $hypId:ident dans $hyp'I:ident)
          pushCom "ou"
          pushTac `(tactic|On réécrit via ← $hypId:ident dans $hyp'I:ident)
          pushCom "On peut aussi s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
          pushTac `(tactic| On combine [$hypId:term, ?_])
          pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités."
    | .ineq _ _le _rel _re => do
      pushCom "L'hypothèse {hyp} est une inégalité"
      if ← decl.toExpr.closesGoal goal then
          pushCom "Cette inégalité est exactement ce qu'il faut démontrer"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|On conclut par $hypId:ident)
      else
        if ← decl.toExpr.linarithClosesGoal goal then
            pushCom "Le but courant en découle immédiatement"
            pushCom "On peut l'utiliser avec :"
            pushTac `(tactic|On conclut par $hypId:ident)
        else do
            pushCom "On peut s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
            pushTac `(tactic| On combine [$hypId:term, ?_])
            pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités ou inégalités."
    | .mem _ _elem _set => do
      pushCom "L'hypothèse {hyp} est une appartenance"
      if ← decl.toExpr.closesGoal goal then
          pushCom "Cette appartenance est exactement ce qu'il faut démontrer"
          pushComment   "On peut l'utiliser avec :"
          pushTac `(tactic|On conclut par $hypId:ident)
    | .prop (.const `False _) => do
        pushComment <| "Cette hypothèse est une contradiction."
        pushCom "On peut en déduire tout ce qu'on veut par :"
        pushTac `(tactic|Montrons une contradiction)
        pushTac `(tactic|On conclut par $hypId:ident)
    | .prop _ => do
        pushCom "Je n'ai rien à déclarer à propos de cette hypothèse."
    | .data e => do
        let t ← toString <$> ppExpr e
        pushComment <| s!"L'objet {hyp}" ++ match t with
          | "ℝ" => " est un nombre réel fixé."
          | "ℕ" => " est un nombre entier naturel fixé."
          | "ℤ" => " est un nombre entier relatif fixé."
          | s => " : " ++ s ++ " est fixé."

def helpAtGoal (goal : MVarId) : SuggestionM Unit :=
  goal.withContext do
  parse (← goal.getType) fun g ↦ match g with
    | .forall_rel _e var_name _typ rel rel_rhs _propo => do
        let py ← ppExpr rel_rhs
        let commun := s!"{var_name}{rel}{py}"
        pushCom "Le but commence par « ∀ {commun} »"
        pushCom "Une démonstration directe commence donc par :"
        pushTactic s!"Soit {commun}"
    | .forall_simple _e var_name typ _propo => do
        let t ← ppExpr typ
        pushCom "Le but commence par « ∀ {var_name} : {t}, »"
        pushCom "Une démonstration directe commence donc par :"
        pushTactic s!"Soit {var_name} : {t}"
    | .exist_rel _e var_name typ _rel _rel_rhs propo => do
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ := Name.mkSimple n₀
        let tgt ← (propo.rename (Name.mkSimple n) nn₀).toStr
        let t ← ppExpr typ
        pushCom "Le but est de la forme « ∃ {n}, ... »"
        pushCom "Une démonstration directe commence donc par :"
        pushTactic s!"Montrons que {n₀} convient : {tgt}"
        pushComment <| s!"en remplaçant {n₀} par " ++ describe t
    | .exist_simple _e var_name typ propo => do
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ := Name.mkSimple n₀
        let tgt ← (propo.rename var_name nn₀).toStr
        let t ← ppExpr typ
        pushCom "Le but est de la forme « ∃ {n}, ... »"
        pushCom "Une démonstration directe commence donc par :"
        pushTactic s!"Montrons que {n₀} convient : {tgt}"
        pushComment <| s!"en remplaçant {n₀} par {describe t}"
    | .conjunction _e propo propo' => do
        let p ← propo.toStr
        let p' ← propo'.toStr
        pushCom "Le but est de la forme « ... et ... »"
        pushCom "Une démonstration directe commence donc par :"
        pushTactic s!"Montrons que {p}"
        pushCom "Une fois cette première démonstration achevée, il restera à montrer que {p'}"
    | .disjunction _e propo propo' => do
        let p ← propo.toStr
        let p' ← propo'.toStr
        pushCom "Le but est de la forme « ... ou ... »"
        pushCom "Une démonstration directe commence donc par annoncer quelle alternative va être démontrée :"
        pushTactic s!"Montrons que {p}"
        pushCom "ou bien :"
        pushTactic s!"Montrons que {p'}"
    | .impl _e le _re lhs _rhs => do
        let l ← lhs.toStr
        let leStx : Term ← Lean.PrettyPrinter.delab le
        pushCom "Le but est une implication « {l} → ... »"
        pushCom "Une démonstration directe commence donc par :"
        let Hyp := mkIdent "hyp"
        pushTac `(tactic| Supposons $Hyp:ident : $leStx)
        pushCom "où hyp est un nom disponible au choix."
    | .iff _e _le _re lhs rhs => do
        let l ← lhs.toStr
        let r ← rhs.toStr
        pushCom "Le but est une équivalence. On peut annoncer la démonstration de l'implication de la gauche vers la droite par :"
        pushTactic s!"Montrons que {l} → {r}"
        pushCom "Une fois cette première démonstration achevée, il restera à montrer que {r} → {l}"
    | .equal _e le re => do
        let l ← ppExpr le
        let r ← ppExpr re
        pushComment $ "Le but est une égalité"
        pushCom "On peut la démontrer par réécriture avec la commande `On réécrit via`"
        pushCom "ou bien commencer un calcul par"
        pushCom "  calc {l} = sorry := by sorry"
        pushCom "  ... = {r} := by sorry"
        pushCom "On peut bien sûr utiliser plus de lignes intermédiaires."
        pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec"
        pushCom "  On combine [hyp₁, hyp₂]"
    | .ineq _e le rel re => do
        let l ← ppExpr le
        let r ← ppExpr re
        pushCom "Le but est une inégalité"
        pushCom "On peut commencer un calcul par"
        pushCom "  calc {l}{rel}sorry := by sorry "
        pushCom "  ... = {r} := by sorry "
        pushCom "On peut bien sûr utiliser plus de lignes intermédiaires."
        pushCom "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité."
        pushCom "De même la première ligne peut être une égalité. Au total les symboles de relations"
        pushCom "doivent s'enchaîner pour donner {rel}"
        pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec"
        pushCom "  On combine [hyp₁, hyp₂]"
    | .prop (.const `False _) => do
        pushComment $ "Le but est de montrer une contradiction."
        pushCom "On peut par exemple appliquer une hypothèse qui est une négation"
        pushCom "c'est à dire, par définition, de la forme P → false."
    | .prop _ | .mem _ _ _ | .data _ => pushCom "Pas d'idée"


 elab "helpAt" h:ident : tactic => do
   let s ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
   logInfo <| "\n".intercalate (s.toList.map toString)

 elab "help" : tactic => do
   let s ← gatherSuggestions (helpAtGoal (← getMainGoal))
   logInfo <| "\n".intercalate (s.toList.map toString)

set_option linter.unusedVariables false

example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  helpAt h
  apply h
  norm_num

example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  helpAt h
  trivial

example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  helpAt h
  trivial

example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  helpAt h
  exact h 2 h'

example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  helpAt h
  exact h 2

example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  helpAt h
  exact h h'

example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  helpAt h
  trivial

example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  helpAt h
  trivial

example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  helpAt h
  trivial

example : True ∧ 1 = 1 := by
  help
  exact ⟨trivial, rfl⟩

example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  helpAt h
  trivial


example : True ∨ false := by
  help
  left
  trivial

example (P : Prop) (h : P) : True := by
  helpAt h
  trivial

example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  helpAt h
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  helpAt h
  Par h appliqué à [2, le_rfl] on obtient n tel que (n_sup : n ≥ 3) (hn : ∀ (l : ℕ), l - n = 0 → P l 2)
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  helpAt h
  trivial


example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  helpAt h
  Par h appliqué à [2, le_rfl] on obtient n' tel que (n_sup : n' ≥ 3) (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  helpAt h
  trivial


example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  helpAt h
  trivial


example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  helpAt h
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  helpAt h
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  helpAt h
  trivial


example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  help
  use 0
  tauto

example (P Q : Prop) (h : Q) : P → Q := by
  help
  exact fun _ ↦ h

example : ∀ n ≥ 0, True := by
  help
  intros
  trivial

example : ∀ n : ℕ, 0 ≤ n := by
  help
  exact Nat.zero_le
