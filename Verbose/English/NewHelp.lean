import Verbose.Tactics.NewHelp
import Verbose.English.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.English

def describe {α : Type} [ToString α] (t : α) : String :=
match toString t with
| "ℝ" => "a real number"
| "ℕ" => "a natural number"
| "ℤ" => "an integer"
| t => "an expression with type " ++ t

def describe_pl {α : Type} [ToString α] (t : α) : String :=
match toString t with
| "ℝ" => "some real numbers"
| "ℕ" => "some natural numbers"
| "ℤ" => "some integers"
| t => "some expressions with type " ++ t

def libre (s: String) : String := s!"The name {s} can be chosen freely among available names."

def libres (ls : List String) : String :=
"The names " ++ String.intercalate ", " ls ++ " can be chosen freely among available names."

def mkFixDecl (var : Name) (typ : Expr) : MetaM (TSyntax `fixDecl) := do
  let i := mkIdent var
  let typS ← Lean.PrettyPrinter.delab typ
  `(fixDecl|$i:ident : $typS)

def helpExistRel (goal : MVarId) (hyp : Name) (hypId : Ident) (var_name : Name) (rel : String) (rel_rhs : Expr) (propo : MyExpr) : SuggestionM Unit := do
  let y ← ppExpr rel_rhs
  let pS ← propo.delab
  let name ← goal.getUnusedUserName var_name
  let nameS := mkIdent name
  let hS := mkIdent s!"h{name}"
  let ineqName := Name.mkSimple s!"{name}{symb_to_hyp rel rel_rhs}"
  let ineqIdent := mkIdent ineqName
  let ineqS ← mkRelStx name rel rel_rhs
  pushCom "The assumption {hyp} has shape « ∃ {var_name}{rel}{y}, ... »"
  pushCom "One can use it with:"
  pushTac `(tactic|By $hypId:term we get $nameS:ident such that ($ineqIdent : $ineqS) ($hS : $pS))
  pushComment <| libres [toString name, s!"{name}{symb_to_hyp rel rel_rhs}", s!"h{name}"]

@[help _ ∧ _]
def helpConjunction : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
    parse hypType fun m ↦ do
      if let .conjunction _ propo propo' := m then
        let h₁N ← goal.getUnusedUserName `h
        let h₁I := mkIdent h₁N
        let h₂N ← goal.getUnusedUserName `h'
        let h₂I := mkIdent h₂N
        let p₁S ← propo.delab
        let p₂S ← propo'.delab
        pushCom "The assumption {hyp} has shape « ... and ... »"
        pushCom "One can use it with:"
        pushTac `(tactic|By $hypId:term we get ($h₁I : $p₁S) ($h₂I : $p₂S))
        pushComment <| libres [s!"{h₁N}", s!"{h₂N}"]
        flush

@[help _ ∨ _]
def helpDisjunction : HelpExt where
  run (_goal : MVarId) (hyp : Name) (hypId : Ident) (_hypType : Expr) : SuggestionM Unit := do
  pushCom "The assumption {hyp} has shape « ... or ... »"
  pushCom "One can use it with:"
  pushTac `(tactic|We proceed using $hypId:term)


@[help _ → _]
def helpImplication : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .impl _ _le re lhs rhs := m then
  let HN ← goal.getUnusedUserName `H
  let HI := mkIdent HN
  let H'N ← goal.getUnusedUserName `H'
  let H'I := mkIdent H'N
  let l ← lhs.delab
  let lStr ← PrettyPrinter.ppTerm l
  let r ← rhs.delab
  pushCom "The assumption {hyp} is an implication"
  if ← re.closesGoal goal then do
    pushCom "The conclusion of this implication is the current goal"
    pushCom "Hence one can use this assumption with:"
    pushTac `(tactic| By $hypId:term it suffices to prove $l)
    flush
    pushCom "If one already has a proof {HN} of {lStr} then one can use:"
    pushTac `(tactic|We conclude by $hypId:term applied to $HI)
  else do
    pushCom "The premiss of this implication is {lStr}"
    pushCom "If you have a proof {HN} of {lStr}"
    pushCom "you can use this assumption with:"
    pushTac `(tactic|By $hypId:term applied to $HI:term we get $H'I:ident : $r:term)
    pushComment <| libre s!"{H'N}"

@[help _ ↔ _]
def helpEquivalence : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .iff _ _le _re lhs rhs := m then
  let l ← lhs.delab
  let lStr ← PrettyPrinter.ppTerm l
  let r ← rhs.delab
  let rStr ← PrettyPrinter.ppTerm r
  let hyp'N ← goal.getUnusedUserName `hyp
  let hyp'I := mkIdent hyp'N
  pushCom "The assumption {hyp} is an equivalence"
  pushCom "One can use it to replace the left-hand-side (namely {lStr}) by the right-hand side (namely {rStr}) in the goal with:"
  pushTac `(tactic|We rewrite using $hypId:term)
  flush
  pushCom "One can use it to replace the right-hand-side in the goal with:"
  pushTac `(tactic|We rewrite using ← $hypId)
  flush
  pushCom "One can also perform such replacements in an assumption {hyp'N} with"
  pushTac `(tactic|We rewrite using $hypId:term at $hyp'I:ident)
  flush
  pushCom "or"
  pushTac `(tactic|We rewrite using ← $hypId:term at $hyp'I:ident)

@[help _ = _]
def helpEqual : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
  let decl := ← getLocalDeclFromUserName hyp
  parse hypType fun m ↦ do
  if let .equal _ le re := m then
  let l ← ppExpr le
  let r ← ppExpr re
  let hyp'N ← goal.getUnusedUserName `hyp
  let hyp'I := mkIdent hyp'N
  pushCom "The assumption {hyp} is an equality"
  if ← decl.toExpr.linarithClosesGoal goal then
    pushComment <| s!"The current goal follows from it immediately"
    pushComment   "One can use it with:"
    pushTac `(tactic|We conclude by $hypId:ident)
  else do
    pushCom "One can use it to replace the left-hand-side (namely {l}) by the right-hand side (namely {r}) in the goal with:"
    pushTac `(tactic|We rewrite using $hypId:ident)
    flush
    pushCom "One can use it to replace the right-hand-side in the goal with:"
    pushTac `(tactic|We rewrite using ← $hypId:ident)
    flush
    pushCom "One can also perform such replacements in an assumption {hyp'N} with"
    pushTac `(tactic|We rewrite using $hypId:ident dans $hyp'I:ident)
    flush
    pushCom "or"
    pushTac `(tactic|We rewrite using ← $hypId:ident dans $hyp'I:ident)
    flush
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic|We combine [$hypId:term, ?_])
    pushCom "replacing the question mark by one or more terms proving equalities."

@[help _ ≤ _, _ < _, _ ≥ _, _ > _]
def helpIneq : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
  let decl := ← getLocalDeclFromUserName hyp
  parse hypType fun m ↦ do
  if let .ineq _ _le _rel _re := m then
  pushCom "The assumption {hyp} is an equality"
  if ← decl.toExpr.linarithClosesGoal goal then
      flush
      pushCom "It immediately implies the current goal."
      pushCom "One can use it with:"
      pushTac `(tactic|We conclude by $hypId:ident)
  else do
      flush
      pushCom "One can also use it in a computation step, or combine it linearly to others with:"
      pushTac `(tactic|We combine [$hypId:term, ?_])
      pushCom "replacing the question mark by one or more terms proving equalities or inequalities."

@[help _ ∈ _]
def helpMem : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .mem _ elem set := m then
  if let some (le, re) := set.memInterPieces? then
    let h₁N ← goal.getUnusedUserName `h
    let h₁I := mkIdent h₁N
    let h₂N ← goal.getUnusedUserName `h'
    let h₂I := mkIdent h₂N
    let p₁S ← PrettyPrinter.delab le
    let p₂S ← PrettyPrinter.delab re
    let elemS ← PrettyPrinter.delab elem
    pushCom "The assumption {hyp} claims membership to an intersection"
    pushCom "One can use it with:"
    pushTac `(tactic|By $hypId:term we get ($h₁I : $elemS ∈ $p₁S) ($h₂I : $elemS ∈ $p₂S))
    pushComment <| libres [s!"{h₁N}", s!"{h₂N}"]
  else if set.memUnionPieces?.isSome then
    pushCom "The assumption {hyp} claims membership to a union"
    pushCom "One can use it with:"
    pushTac `(tactic|We proceed using $hypId)
  else
    pushCom "The assumption {hyp} is a membership"

@[help False]
def helpFalse : HelpExt where
  run (_goal : MVarId) (_hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .prop (.const `False _) := m then
  pushComment <| "This assumption is a contradiction."
  pushCom "One can deduce anything from it with:"
  pushTac `(tactic|(Let's prove it's contradictory
                    We conclude by $hypId:ident))

@[help _ ⊆ _]
def helpSubset : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .subset _ lhs rhs := m then
  let ambientTypeE := (← instantiateMVars (← inferType lhs)).getAppArgs[0]!
  let ambientTypePP ← ppExpr ambientTypeE
  let l ← ppExpr lhs
  let r ← ppExpr rhs
  let rT ← PrettyPrinter.delab rhs
  let xN ← goal.getUnusedUserName `x
  let xI := mkIdent xN
  let hxN ← goal.getUnusedUserName `hx
  let hxI := mkIdent hxN
  let hx'N ← goal.getUnusedUserName `hx'
  let hx'I := mkIdent hx'N
  pushCom "The assumption {hyp} ensures the inclusion of {l} in {r}."
  pushCom "One can use it with:"
  pushTac `(tactic| By $hypId:ident applied to $xI using $hxI we get $hx'I:ident : $xI ∈ $rT)
  pushCom "where {xN} is {describe ambientTypePP} and {hxN} proves that {xN} ∈ {l}"

def helpAtHyp (goal : MVarId) (hyp : Name) : SuggestionM Unit :=
  goal.withContext do
  let decl := ← getLocalDeclFromUserName hyp
  let hypId := mkIdent hyp
  if ← decl.type.closesGoal goal then
    pushCom "This assumption is exactly what needs to be proven"
    pushCom "One can use it with:"
    pushTac `(tactic|We conclude by $hypId:ident)
    return
  let mut hypType ← instantiateMVars decl.type
  if ← hypType.isAppFnUnfoldable then
    if let some expandedHypType ← hypType.expandHeadFun then
      let expandedHypTypeS ← PrettyPrinter.delab expandedHypType
      pushCom "This assumption starts with the application of a definition."
      pushCom "One can explicit it with:"
      pushTac `(tactic|We reformulate $hypId:ident as $expandedHypTypeS)
      flush
      hypType := expandedHypType
  parse hypType fun m ↦ match m with
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
          pushCom "The assumption {hyp} starts with « ∀ {n}{rel}{py}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ... »"
          pushCom "One can use it with:"
          pushTac `(tactic|By $hypId:term applied to $n₀T using $hn₀T we get $(mkIdent var_name'):ident such that ($ineqIdent : $ineqS) ($hn'S : $p'S))
          pushCom "where {n₀} is {describe t} and {hn₀N} is a proof of the fact that {nn₀}{rel}{py}."
          pushComment <| libres [s!"{var_name'}", s!"{var_name'}{symb_to_hyp rel' rel_rhs'}", s!"h{var_name'}"]
        | .exist_simple _e' var_name' _typ' propo' => do
          let n' := toString var_name'
          let var_name' := ← goal.getUnusedUserName var_name'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "The assumption {hyp} starts with « ∀ {n}{rel}{py}, ∃ {n'}, ... »"
          pushCom "One can use it with:"
          pushTac `(tactic|By $hypId:term applied to $n₀T using $hn₀T we get $(mkIdent var_name'):ident such that ($hn'S : $p'S))
          pushCom "where {n₀} is {describe t} and h{n₀} is a proof of the fact that {n₀}{rel}{py}"
          pushComment <| libres [n', s!"h{n'}"]
        | _ => do
          let pS ← propo.delab
          pushCom "The assumption {hyp} starts with « ∀ {var_name}{rel}{py}, »"
          pushCom "One can use it with:"
          pushTac `(tactic|By $hypId:term applied to $n₀T using $hn₀T we get ($hn₀T : $pS))
          pushCom "where {n₀} is {describe t} and h{n₀} is a proof of the fact that {n₀}{rel}{py}"
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
          pushCom "The assumption {hyp} starts with « ∀ {n}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ... »"
          pushCom "One can use it with:"
          pushTac `(tactic|By $hypId:term applied to $n₀T we get $(mkIdent var_name'):ident such that ($ineqIdent : $ineqS) ($hn'S : $p'S))
          pushCom "where {n₀} is {describe t}"
          pushComment <| libres [s!"{var_name'}", s!"{var_name'}{symb_to_hyp rel' rel_rhs'}", s!"h{var_name'}"]
        | .exist_simple _e' var_name' _typ' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "The assumption {hyp} starts with « ∀ {n}, ∃ {var_name'}, ... »"
          pushCom "One can use it with:"
          pushTac `(tactic|By $hypId:term applied to $n₀T we get $(mkIdent var_name'):ident such that ($hn'S : $p'S))
          pushCom "where {n₀} is {describe t}"
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
          pushCom "The assumption {hyp} starts with « ∀ {n} {n'}, {rel} → ... "
          pushCom "One can use it with:"
          pushTac `(tactic|By $hypId:term applied to [$n₀T, $n'₀T, $HT] we get ($hT : $p'S))
          pushCom "where {nn₀} and {var_name'₀} are {describe_pl t} and {H} is a proof of {rel₀}"
          pushComment <| libre (toString h)
        | _ => do
          let pS ← propo.delab
          pushCom "The assumption {hyp} starts with « ∀ {n}, »"
          pushCom "One can use it with:"
          pushTac `(tactic|By $hypId:term applied to $n₀T we get ($hn₀T : $pS))
          pushCom "where {n₀} is {describe t}"
          pushComment <| libre "h" ++ ""
          flush
          pushCom "If this assumption won't be used again in its general shape, one can also specialize {hyp} with"
          pushTac `(tactic|We apply $hypId:ident to $n₀T)
          -- **TODO** cleanup this mess
          let msgM : MetaM (Option <| TSyntax `tactic) := withoutModifyingState do
              (do
              let _ ← goal.apply decl.toExpr
              let prf ← instantiateMVars (mkMVar goal)
              let prfS ← prf.toMaybeApplied
              if !prf.hasMVar then
                some (← `(tactic|We conclude by $prfS))
              else
                none)
            <|>
              pure none
          let msg ← msgM
          if let some msg := msg then
            let but ← ppExpr (← goal.getType)
            flush
            pushCom "\nSince the goal is {but}, one can use:"
            pushTac (do return msg)
    | .exist_rel _ var_name _typ rel rel_rhs propo => do
      helpExistRel goal hyp hypId var_name rel rel_rhs propo
    | .exist_simple _ var_name _typ propo => do
      let pS ← propo.delab
      let name ← goal.getUnusedUserName var_name
      let nameS := mkIdent name
      let hS := mkIdent s!"h{name}"
      pushCom "The assumption {hyp} has shape « ∃ {var_name}, ... »"
      pushCom "One can use it with:"
      pushTac `(tactic|By $hypId:term we get $nameS:ident such that ($hS : $pS))
      pushComment <| libres [toString name, s!"h{name}"]
    | .data e => do
      let t ← toString <$> ppExpr e
      pushComment <| s!"The object {hyp}" ++ match t with
        | "ℝ" => " is a fixed real number."
        | "ℕ" => " is a fixed natural number."
        | "ℤ" => " is a fixed integer."
        | s => " : " ++ s ++ " is fixed."
    | _ => do
      for ext in ← (helpExt.getState (← getEnv)).2.getMatch hypType discrTreeConfig do
        try
          ext.run goal hyp hypId hypType
          flush
        catch _ =>
          pure ()
      if (← get).suggestions.isEmpty then
        pushCom "I have nothing to say about this assumption."
        flush

def helpAtGoal (goal : MVarId) : SuggestionM Unit :=
  goal.withContext do
  let mut goalType ← instantiateMVars (← goal.getType)
  if ← goalType.isAppFnUnfoldable then
    if let some expandedGoalType ← goalType.expandHeadFun then
      let expandedGoalTypeS ← PrettyPrinter.delab expandedGoalType
      pushCom "The goal starts with the application of a definition."
      pushCom "One can explicit it with:"
      pushTac `(tactic|Let's prove that $expandedGoalTypeS)
      flush
      goalType := expandedGoalType
  if goalType.getAppFn matches .const `goalBlocker .. then
    let actualGoal := goalType.getAppArgs[0]!
    let actualGoalS ← PrettyPrinter.delab actualGoal
    pushCom "The next step is to announce:"
    pushTac `(tactic| Let's now prove that $actualGoalS)
    return
  parse goalType fun g ↦ match g with
    | .forall_rel _e var_name _typ rel rel_rhs _propo => do
        let py ← ppExpr rel_rhs
        let n ← goal.getUnusedUserName var_name
        let ineqS ← mkFixDeclIneq n rel rel_rhs
        let commun := s!"{var_name}{rel}{py}"
        pushCom "The goal starts with « ∀ {commun} »"
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic|Fix $ineqS)
    | .forall_simple _e var_name typ _propo => do
        let t ← ppExpr typ
        let n ← goal.getUnusedUserName var_name
        let declS ← mkFixDecl n typ
        pushCom "The goal starts with « ∀ {var_name} : {t}, »"
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic|Fix $declS)
    | .exist_rel _e var_name typ rel rel_rhs propo => do
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀S := mkIdent nn₀
        withRenamedFVar var_name nn₀ do
        let ineqS ← mkRelStx nn₀ rel rel_rhs
        let tgtS ← propo.delab
        let fullTgtS ← `($ineqS ∧ $tgtS)
        let t ← ppExpr typ
        pushCom "The goal has shape « ∃ {n}{rel}{← ppExpr rel_rhs}, ... »"
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic|Let's prove that $n₀S works : $fullTgtS)
        pushCom "replacing {n₀} by {describe t}"
    | .exist_simple _e var_name typ propo => do
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀S := mkIdent nn₀
        withRenamedFVar var_name nn₀ do
        let tgt ← propo.delab
        let t ← ppExpr typ
        pushCom "The goal has shape « ∃ {n}, ... »"
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic|Let's prove that $n₀S works : $tgt)
        pushCom "replacing {n₀} by {describe t}"
    | .conjunction _e propo propo' => do
        let pS ← propo.delab
        let p ← PrettyPrinter.ppTerm pS
        let p'S ← propo'.delab
        let p' ← PrettyPrinter.ppTerm p'S
        pushCom "The goal has shape « ... and ... »"
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic|Let's first prove that $pS)
        pushCom "After finish this first proof, it will remain to prove that {p'}"
        flush
        pushCom "One can also start with"
        pushTac `(tactic|Let's first prove that $p'S)
        pushCom "then, after finishing this first proof, il will remain to prove that {p}"
    | .disjunction _e propo propo' => do
        let pS ← propo.delab
        let p'S ← propo'.delab
        pushCom "The goal has shape « ... ou ... »"
        pushCom "Hence a direct proof starts with announcing which alternative will be proven:"
        pushTac `(tactic|Let's prove that $pS)
        flush
        pushCom "or:"
        pushTac `(tactic|Let's prove that $p'S)
    | .impl _e le _re lhs _rhs => do
        let l ← ppExpr le
        let leStx ← lhs.delab
        let Hyp := mkIdent (← goal.getUnusedUserName `hyp)
        pushCom "The goal is une implication « {l} → ... »"
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic| Assume $Hyp:ident : $leStx)
        pushCom "where hyp is a chosen available name."
    | .iff _e le re lhs rhs => do
        let l ← ppExpr le
        let lS ← lhs.delab
        let r ← ppExpr re
        let rS ← rhs.delab
        pushCom "The goal is an equivalence. One can announce the proof of the left to right implication with:"
        pushTac `(tactic|Let's prove that $lS → $rS)
        pushCom "After proving this first statement, it will remain to prove that {r} → {l}"
        flush
        pushCom "One can also start with"
        pushTac `(tactic|Let's prove that $rS → $lS)
        pushCom "then, after finishing this first proof, il will remain to prove that {l} → {r}"
    | .equal _e le re => do
        let ambiantTypeE ← instantiateMVars (← inferType le)
        let l ← ppExpr le
        let lS ← PrettyPrinter.delab le
        let r ← ppExpr re
        let rS ← PrettyPrinter.delab re
        if ambiantTypeE.isApp && ambiantTypeE.isAppOf `Set then
          pushCom "The goal is a set equality"
          pushCom "One can prove it by rewriting with `We rewrite using`"
          pushCom "or start a computation using"
          pushCom "  calc {l} = sorry := by sorry"
          pushCom "  ... = {r} := by sorry"
          pushCom "One can also prove it by double inclusion."
          pushCom "In this case the proof starts with:"
          pushTac `(tactic|Let's first prove that $lS ⊆ $rS)
        else
          -- **FIXME** this discussion isn't easy to do using tactics.
          pushCom "The goal is an equality"
          pushCom "One can prove it by rewriting with `We rewrite using`"
          pushCom "or start a computation using"
          pushCom "  calc {l} = sorry := by sorry"
          pushCom "  ... = {r} := by sorry"
          pushCom "Of course one can have more intermediate steps."
          pushCom "One can also make linear combination of assumptions hyp₁ hyp₂... with"
          pushCom "  We combine [hyp₁, hyp₂]"
    | .ineq _e le rel re => do
        let l ← ppExpr le
        let r ← ppExpr re
        -- **FIXME** this discussion isn't easy to do using tactics.
        pushCom "The goal is an inequality"
        pushCom "One can start a computation using"
        pushCom "  calc {l}{rel}sorry := by sorry "
        pushCom "  ... = {r} := by sorry "
        pushCom "Of course one can have more intermediate steps."
        pushCom "The last computation line is not necessarily an equality, it can be an inequality."
        pushCom "Similarly the first line could be an equality. In total, the relation symbols"
        pushCom "must chain to give {rel}"
        pushCom "One can also make linear combination of assumptions hyp₁ hyp₂... with"
        pushCom "  We combine [hyp₁, hyp₂]"
    | .mem _ elem set => do
      if let some (le, _) := set.memInterPieces? then
        let p₁S ← PrettyPrinter.delab le
        let elemS ← PrettyPrinter.delab elem
        pushCom "The goal is prove {← ppExpr elem} belongs to the intersection of {← ppExpr le} with another set."
        pushCom "Hance a direct proof starts with:"
        pushTac `(tactic|Let's first prove that $elemS ∈ $p₁S)
      else if let some (le, re) := set.memUnionPieces? then
        let p₁S ← PrettyPrinter.delab le
        let p₂S ← PrettyPrinter.delab re
        let elemS ← PrettyPrinter.delab elem
        pushCom "The goal is to prove {← ppExpr elem} belongs to the union of {← ppExpr le} and {← ppExpr re}."
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic|Let's prove that $elemS ∈ $p₁S)
        flush
        pushCom "or by:"
        pushTac `(tactic|Let's prove that $elemS ∈ $p₂S)
      else
        pushCom "No idea"
    | .subset _e lhs rhs => do
        let l ← ppExpr lhs
        let r ← ppExpr rhs
        let lT ← PrettyPrinter.delab lhs
        let xN ← goal.getUnusedUserName `x
        let xI := mkIdent xN
        pushCom "The goal is the inclusion {l} ⊆ {r}"
        pushCom "Hence a direct proof starts with:"
        pushTac `(tactic| Fix $xI:ident ∈ $lT)
        pushComment <| libre s!"{xN}"
    | .prop (.const `False _) => do
        pushCom "The goal is to prove a contradiction."
        pushCom "One can apply an assumption which is a negation"
        pushCom "namely, by definition, with shape P → false."
    | .prop _ | .data _ => pushCom "No idea"

open Lean.Parser.Tactic in
elab "help" h:(colGt ident)? : tactic => do
match h with
| some h => do
        let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
        if s.isEmpty then
          logInfo (msg.getD "No suggestion")
        else
          Std.Tactic.TryThis.addSuggestions (← getRef) s (header := "Help")
| none => do
   let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
   if s.isEmpty then
          logInfo (msg.getD "No suggestion")
    else
      Std.Tactic.TryThis.addSuggestions (← getRef) s (header := "Help")

set_option linter.unusedVariables false

/--
info: Help
• By h applied to n₀ using hn₀ we get (hn₀ : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  help h
  apply h
  norm_num

/--
info: Help
• By h we get n such that (n_pos : n > 0) (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  help h
  trivial

/--
info: Help
• By h we get ε such that (ε_pos : ε > 0) (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  help h
  trivial

/--
info: Help
• By h applied to n₀ we get (hn₀ : P n₀ ⇒ Q n₀)
• We apply h to n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  help h
  exact h 2 h'

/--
info: Help
• By h applied to n₀ we get (hn₀ : P n₀)
• We apply h to n₀
• We conclude by h applied to 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  help h
  exact h 2

/--
info: Help
• By h it suffices to prove P 1
• We conclude by h applied to H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  help h
  exact h h'

/--
info: Help
• By h applied to H we get H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  help h
  trivial

/--
info: Help
• By h we get (h_1 : P 1) (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  help h
  trivial

/--
info: Help
• We rewrite using h
• We rewrite using ← h
• We rewrite using h at hyp
• We rewrite using ← h at hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  help h
  trivial

/--
info: Help
• Let's first prove that True
• Let's first prove that 1 = 1
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  help
  exact ⟨trivial, rfl⟩

/--
info: Help
• We proceed using h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  help h
  trivial

/--
info: Help
• Let's prove that True
• Let's prove that False
-/
#guard_msgs in
example : True ∨ False := by
  help
  left
  trivial

/-- info: I have nothing to say about this assumption. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  help h
  trivial

/--
info: Help
• (
  Let's prove it's contradictory
  We conclude by h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  help h
  trivial

/--
info: Help
• By h applied to H we get H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n such that (n_sup : n ≥ 3) (hn : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to [k₀, n₀, H] we get (h_1 : ∀ (l : ℕ), l - n₀ = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n_1 such that (n_1_sup : n_1 ≥ 3) (hn_1 : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h we get n such that (n_sup : n ≥ 5) (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n such that (n_sup : n ≥ 3) (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  help h
  trivial

/--
info: Help
• By h we get n such that (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ we get n such that (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n such that (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
• Let's prove that n₀ works: P n₀ ⇒ True
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  help
  use 0
  tauto

/--
info: Help
• Assume hyp : P
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  help
  exact fun _ ↦ h

/--
info: Help
• Fix n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  help
  intros
  trivial

/--
info: Help
• Fix n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  help
  exact Nat.zero_le

/--
info: Help
• Let's prove that n₀ works: 0 ≤ n₀
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  help
  use 1
  exact Nat.zero_le 1

/--
info: Help
• Let's prove that n₀ works: n₀ ≥ 1 ∧ True
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  help
  use 1

/-- info: I have nothing to say about this assumption. -/
#guard_msgs in
example (h : Odd 3) : True := by
  help h
  trivial

/--
info: Help
• Fix x ∈ s
---
info: Help
• By h applied to x_1 using hx we get hx' : x_1 ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  help
  Fix x ∈ s
  help h
  exact h x_mem

/--
info: Help
• By h we get (h_1 : x ∈ s) (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  help h
  By h we get (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Help
• By h we get (h_1 : x ∈ s) (h' : x ∈ t)
---
info: Help
• Let's first prove that x ∈ t
---
info: Help
• Let's now prove that x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  help h
  By h we get (h_1 : x ∈ s) (h' : x ∈ t)
  help
  Let's first prove that x ∈ t
  exact h'
  help
  Let's now prove that x ∈ s
  exact h_1

/--
info: Help
• We proceed using h
---
info: Help
• Let's prove that x ∈ t
• Let's prove that x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  help h
  We proceed using h
  Assume hyp : x ∈ s
  help
  Let's prove that x ∈ s
  exact hyp
  Assume hyp : x ∈ t
  Let's prove that x ∈ t
  exact  hyp
