import Verbose.Tactics.HelpExtension
import Verbose.English.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.English

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "a real number"
| "ℕ" => "a natural number"
| "ℤ" => "an integer"
| t => "an expression with type " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "some real numbers"
| "ℕ" => "some natural numbers"
| "ℤ" => "some integers"
| t => "some expressions with type " ++ t

def libre (s: String) : String := s!"The name {s} can be chosen freely among available names."

def libres (ls : List String) : String :=
"The names " ++ String.intercalate ", " ls ++ " can be chosen freely among available names."

alias _root_.Lean.Name.ident := Lean.mkIdent
alias _root_.Lean.Expr.fmt := Lean.PrettyPrinter.ppExpr
alias _root_.Lean.Expr.stx := Lean.PrettyPrinter.delab

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} has shape “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} starts with “{headDescr}”"

/-- If the given expression can be applied to prove the given goal,
without creating meta-variables, then return the instantiated proof,
otherwise return `None`. -/
def _root_.Lean.Expr.applyToGoal (e : Expr) (goal : MVarId) : MetaM (Option Expr) :=
  withoutModifyingState do
  let _ ← goal.apply e
  let prf ← instantiateMVars (mkMVar goal)
  return if prf.hasMVar then none else some prf

endpoint helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $nameS:ident such that ($ineqIdent : $ineqS) ($hS : $pS))
  pushComment <| libres <| [nameS, ineqIdent, hS].map toString

def helpExistRel (goal : MVarId) (hyp : Name) (var_name : Name) (rel : String) (rel_rhs : Expr) (propo : MyExpr) : SuggestionM Unit := do
  let y ← ppExpr rel_rhs
  let pS ← propo.delab
  let name ← goal.getUnusedUserName var_name
  let nameS := mkIdent name
  let hS := mkIdent s!"h{name}"
  let ineqName := Name.mkSimple s!"{name}{symb_to_hyp rel rel_rhs}"
  let ineqIdent := mkIdent ineqName
  let ineqS ← mkRelStx name rel rel_rhs
  helpExistRelSuggestion hyp s!"∃ {var_name}{rel}{y}, ..." nameS ineqIdent hS ineqS pS

endpoint helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... and ..."
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [s!"{h₁I}", s!"{h₂I}"]

@[help _ ∧ _]
def helpConjunction : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
    parse hypType fun m ↦ do
      if let .conjunction _ propo propo' := m then
        let h₁N ← goal.getUnusedUserName `h
        let h₁I := mkIdent h₁N
        let h₂N ← goal.getUnusedUserName `h'
        let h₂I := mkIdent h₂N
        let p₁S ← propo.delab
        let p₂S ← propo'.delab
        helpConjunctionSuggestion hyp h₁I h₂I p₁S p₂S

endpoint helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "The assumption {hyp} has shape « ... or ... »"
  pushCom "One can use it with:"
  pushTac `(tactic|We proceed using $hyp.ident:term)

@[help _ ∨ _]
def helpDisjunction : HelpExt where
  run (_goal : MVarId) (hyp : Name) (_hypType : Expr) : SuggestionM Unit := do
  helpDisjunctionSuggestion hyp

endpoint helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an implication"
  if closes then do
    pushCom "The conclusion of this implication is the current goal"
    pushCom "Hence one can use this assumption with:"
    pushTac `(tactic| By $hyp.ident:term it suffices to prove $(← le.stx))
    flush
    pushCom "If one already has a proof {HN} of {← le.fmt} then one can use:"
    pushTac `(tactic|We conclude by $hyp.ident:term applied to $HN.ident)
  else do
    pushCom "The premiss of this implication is {← le.fmt}"
    pushCom "If you have a proof {HN} of {← le.fmt}"
    pushCom "you can use this assumption with:"
    pushTac `(tactic|By $hyp.ident:term applied to $HN.ident:term we get $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre s!"{H'N}"

@[help _ → _]
def helpImplication : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .impl _ le re _lhs _rhs := m then
  let HN ← goal.getUnusedUserName `H
  let H'N ← goal.getUnusedUserName `H'
  let closes ← re.closesGoal goal
  helpImplicationSuggestion hyp HN H'N closes le re

endpoint helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equivalence"
  pushCom "One can use it to replace the left-hand-side (namely {← l.fmt}) by the right-hand side (namely {← r.fmt}) in the goal with:"
  pushTac `(tactic|We rewrite using $hyp.ident:term)
  flush
  pushCom "One can use it to replace the right-hand-side in the goal with:"
  pushTac `(tactic|We rewrite using ← $hyp.ident)
  flush
  pushCom "One can also perform such replacements in an assumption {hyp'N} with"
  pushTac `(tactic|We rewrite using $hyp.ident:term at $hyp'N.ident:ident)
  flush
  pushCom "or"
  pushTac `(tactic|We rewrite using ← $hyp.ident:term at $hyp'N.ident:ident)

@[help _ ↔ _]
def helpEquivalence : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .iff _ le re _lhs _rhs := m then
  let hyp'N ← goal.getUnusedUserName `hyp
  helpEquivalenceSuggestion hyp hyp'N le re

endpoint helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : Expr) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equality"
  if closes then
    pushComment <| s!"The current goal follows from it immediately"
    pushComment   "One can use it with:"
    pushTac `(tactic|We conclude by $hyp.ident:ident)
  else do
    pushCom "One can use it to replace the left-hand-side (namely {← l.fmt}) by the right-hand side (namely {← r.fmt}) in the goal with:"
    pushTac `(tactic|We rewrite using $hyp.ident:ident)
    flush
    pushCom "One can use it to replace the right-hand-side in the goal with:"
    pushTac `(tactic|We rewrite using ← $hyp.ident:ident)
    flush
    pushCom "One can also perform such replacements in an assumption {hyp'} with"
    pushTac `(tactic|We rewrite using $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "or"
    pushTac `(tactic|We rewrite using ← $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic|We combine [$hyp.ident:term, ?_])
    pushCom "replacing the question mark by one or more terms proving equalities."

@[help _ = _]
def helpEqual : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
    let decl := ← getLocalDeclFromUserName hyp
    parse hypType fun m ↦ do
    if let .equal _ le re := m then
    let hyp' ← goal.getUnusedUserName `hyp
    let closes ← decl.toExpr.linarithClosesGoal goal
    helpEqualSuggestion hyp hyp' closes le re

endpoint helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equality"
  if closes then
      flush
      pushCom "It immediately implies the current goal."
      pushCom "One can use it with:"
      pushTac `(tactic|We conclude by $hyp.ident:ident)
  else do
      flush
      pushCom "One can also use it in a computation step, or combine it linearly to others with:"
      pushTac `(tactic|We combine [$hyp.ident:term, ?_])
      pushCom "replacing the question mark by one or more terms proving equalities or inequalities."

@[help _ ≤ _, _ < _, _ ≥ _, _ > _]
def helpIneq : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
    let closes ← (← getLocalDeclFromUserName hyp).toExpr.linarithClosesGoal goal
    parse hypType fun m ↦ do
    if let .ineq _ _le _rel _re := m then
    helpIneqSuggestion hyp closes

endpoint helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} claims membership to an intersection"
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [s!"{h₁}", s!"{h₂}"]

endpoint helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} claims membership to a union"
  pushCom "One can use it with:"
  pushTac `(tactic|We proceed using $hyp.ident)

endpoint helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is a membership"

@[help _ ∈ _]
def helpMem : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .mem _ elem set := m then
  if let some (le, re) := set.memInterPieces? then
    let h₁ ← goal.getUnusedUserName `h
    let h₂ ← goal.getUnusedUserName `h'
    let p₁S ← PrettyPrinter.delab le
    let p₂S ← PrettyPrinter.delab re
    let elemS ← PrettyPrinter.delab elem
    helpMemInterSuggestion hyp h₁ h₂ elemS p₁S p₂S
  else if set.memUnionPieces?.isSome then
    helpMemUnionSuggestion hyp
  else
    helpGenericMemSuggestion hyp

endpoint helpContradictiomSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "This assumption is a contradiction."
  pushCom "One can deduce anything from it with:"
  pushTac `(tactic|(Let's prove it's contradictory
                    We conclude by $hypId:ident))
@[help False]
def helpFalse : HelpExt where
  run (_goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .prop (.const `False _) := m then
  helpContradictiomSuggestion hyp.ident

endpoint helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "The assumption {hyp} ensures the inclusion of {l} in {← r.fmt}."
  pushCom "One can use it with:"
  pushTac `(tactic| By $hyp.ident:ident applied to $x.ident using $hx.ident we get $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "where {x} is {describe ambientTypePP} and {hx} proves that {x} ∈ {l}"

@[help _ ⊆ _]
def helpSubset : HelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit := do
  parse hypType fun m ↦ do
  if let .subset _ lhs rhs := m then
  let ambientTypeE := (← instantiateMVars (← inferType lhs)).getAppArgs[0]!
  let ambientTypePP ← ppExpr ambientTypeE
  let l ← ppExpr lhs
  let xN ← goal.getUnusedUserName `x
  let hxN ← goal.getUnusedUserName `hx
  let hx'N ← goal.getUnusedUserName `hx'
  helpSubsetSuggestion hyp xN hxN hx'N rhs l ambientTypePP

endpoint assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "This assumption is exactly what needs to be proven"
  pushCom "One can use it with:"
  pushTac `(tactic|We conclude by $hypId:ident)

endpoint assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) : SuggestionM Unit := do
  pushCom "This assumption starts with the application of a definition."
  pushCom "One can explicit it with:"
  pushTac `(tactic|We reformulate $hypId:ident as $expandedHypTypeS)
  flush

endpoint helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name) (headDescr hypDescr : String) (t : Format)
    (hn'S ineqIdent : Ident) (ineqS p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $(n₀.ident) using $(hn₀.ident) we get $(mkIdent var_name'):ident such that ($ineqIdent : $ineqS) ($hn'S : $p'S))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {hypDescr}."
  pushComment <| libres [s!"{var_name'}", s!"{ineqIdent}", s!"h{var_name'}"]

endpoint helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name) (headDescr n₀rel : String) (t : Format)
    (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get $(n'.ident):ident such that ($hn'.ident : $p'S))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libres [s!"{n'}", s!"{hn'}"]

endpoint helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name) (headDescr n₀rel : String) (t : Format) (newsI : Ident)
    (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get ($newsI : $pS))
  pushCom "where {n₀} is {describe t} and h{n₀} is a proof of the fact that {n₀rel}"
  pushComment <| libre s!"{newsI}"

endpoint helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name) (headDescr : String) (t : Format)
    (hn'S ineqIdent : Ident) (ineqS p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get $var_name'.ident:ident such that ($ineqIdent : $ineqS) ($hn'S : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [s!"{var_name'}", s!"{ineqIdent}", s!"{hn'S}"]

endpoint helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name) (headDescr : String) (t : Format)
    (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get $var_name'.ident:ident such that ($hn'.ident : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [toString var_name', s!"{hn'}"]

endpoint helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name) (headDescr rel₀ : String) (t : Format)
    (p'S : Term) : SuggestionM Unit := do
  pushCom "The assumption {hyp} starts with “{headDescr}"
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to [$nn₀.ident, $var_name'₀.ident, $H.ident] we get ($h.ident : $p'S))
  pushCom "where {nn₀} and {var_name'₀} are {describe_pl t} and {H} is a proof of {rel₀}"
  pushComment <| libre (toString h)

endpoint helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String) (t : Format)
    (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get ($hn₀.ident : $pS))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libre s!"{hn₀}"
  flush
  pushCom "If this assumption won't be used again in its general shape, one can also specialize {hyp} with"
  pushTac `(tactic|We apply $hyp.ident:ident to $nn₀.ident)

endpoint helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format): SuggestionM Unit := do
  let prfS ← prf.toMaybeApplied
  pushCom "Since the goal is {but}, one can use:"
  pushTac `(tactic|We conclude by $prfS)

endpoint helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String) (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $n.ident:ident such that ($hn.ident : $pS))
  pushComment <| libres [toString n, s!"{hn}"]

endpoint helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"The object {hyp}" ++ match t with
    | "ℝ" => " is a fixed real number."
    | "ℕ" => " is a fixed natural number."
    | "ℤ" => " is a fixed integer."
    | s => s!" : {s} is fixed."

endpoint helpNothingSuggestion : SuggestionM Unit := do
  pushCom "I have nothing to say about this assumption."
  flush

def helpAtHyp (goal : MVarId) (hyp : Name) : SuggestionM Unit :=
  goal.withContext do
  let decl := ← getLocalDeclFromUserName hyp
  let hypId := mkIdent hyp
  if ← decl.type.closesGoal goal then
    assumptionClosesSuggestion hypId
    return
  let mut hypType ← instantiateMVars decl.type
  if ← hypType.isAppFnUnfoldable then
    if let some expandedHypType ← hypType.expandHeadFun then
      let expandedHypTypeS ← PrettyPrinter.delab expandedHypType
      assumptionUnfoldingSuggestion hypId expandedHypTypeS
      hypType := expandedHypType
  parse hypType fun m ↦ match m with
    | .forall_rel _ var_name typ rel rel_rhs propo => do
        let py ← ppExpr rel_rhs
        let t ← ppExpr typ
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let hn₀N ← goal.getUnusedUserName ("h" ++ n₀ : String)
        withRenamedFVar var_name nn₀ do
        match propo with
        | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let ineqIdent := mkIdent s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
          let ineqS ← mkRelStx var_name' rel' rel_rhs'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          let headDescr := s!"∀ {n}{rel}{py}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ..."
          let hypDescr := s!"{nn₀}{rel}{py}"
          helpForAllRelExistsRelSuggestion hyp var_name' n₀ hn₀N headDescr hypDescr t hn'S ineqIdent ineqS p'S
        | .exist_simple _e' var_name' _typ' propo' => do
          let n' := ← goal.getUnusedUserName var_name'
          let hn' := Name.mkSimple s!"h{var_name'}"
          let p'S ← propo'.delab
          let headDescr := s!"∀ {n}{rel}{py}, ∃ {var_name'}, ..."
          let n₀rel := s!"{n₀}{rel}{py}"
          helpForAllRelExistsSimpleSuggestion hyp n' hn' n₀ hn₀N headDescr n₀rel t p'S
        | _ => do
          let newsI := (← goal.getUnusedUserName `hyp).ident
          let pS ← propo.delab
          let headDescr := s!"∀ {n}{rel}{py}, ..."
          let n₀rel := s!"{n₀}{rel}{py}"
          helpForAllRelGenericSuggestion hyp n₀ hn₀N headDescr n₀rel t newsI pS
    | .forall_simple _ var_name typ propo => do
        let t ← ppExpr typ
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let hn₀ ← goal.getUnusedUserName ("h" ++ n₀ : String)
        withRenamedFVar var_name nn₀ do
        match propo with
        | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
          let var_name' ← goal.getUnusedUserName var_name'
          let ineqIdent := mkIdent s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
          let ineqS ← mkRelStx var_name' rel' rel_rhs'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          let headDescr := s!"{n}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ..."
          helpForAllSimpleExistsRelSuggestion hyp var_name' nn₀ headDescr t hn'S ineqIdent ineqS p'S
        | .exist_simple _e' var_name' _typ' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let hn' := Name.mkSimple s!"h{var_name'}"
          let p'S ← propo'.delab
          let headDescr := s!"∀ {n}, ∃ {var_name'}, ..."
          helpForAllSimpleExistsSimpleSuggestion hyp var_name' hn' nn₀  headDescr t p'S
        | .forall_rel _e' var_name' _typ' rel' _rel_rhs' propo' => do
          let n' := toString var_name'
          let var_name'₀ := ← goal.getUnusedUserName (Name.mkSimple ((toString var_name') ++ "₀"))
          withRenamedFVar var_name' var_name'₀ do
          let H ← goal.getUnusedUserName `H
          let h ← goal.getUnusedUserName `h
          let rel := n ++ rel' ++ n'
          let rel₀ := s!"{nn₀}{rel'}{var_name'₀}"
          let p'S ← propo'.delab
          let headDescr := s!"∀ {n} {n'}, {rel} ⇒ ..."
          helpForAllSimpleForAllRelSuggestion hyp nn₀ var_name'₀ H h headDescr rel₀ t p'S
        | _ => do
          let pS ← propo.delab
          let headDescr := s!"∀ {n}, ..."
          helpForAllSimpleGenericSuggestion hyp nn₀ hn₀ headDescr t pS
          if let some prf ← decl.toExpr.applyToGoal goal then
            flush
            let but ← ppExpr (← goal.getType)
            helpForAllSimpleGenericApplySuggestion prf but
    | .exist_rel _ var_name _typ rel rel_rhs propo => do
      helpExistRel goal hyp var_name rel rel_rhs propo
    | .exist_simple _ var_name _typ propo => do
      let pS ← propo.delab
      let n ← goal.getUnusedUserName var_name
      let hn := Name.mkSimple s!"h{n}"
      let headDescr := s!"∃ {var_name}, ..."
      helpExistsSimpleSuggestion hyp n hn headDescr pS
    | .data e => do
      let t ← ppExpr e
      helpDataSuggestion hyp t
    | _ => do
      for ext in ← (helpExt.getState (← getEnv)).2.getMatch hypType discrTreeConfig do
        try
          ext.run goal hyp hypType
          flush
        catch _ =>
          pure ()
      if (← get).suggestions.isEmpty then
        helpNothingSuggestion

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
• By h applied to n₀ using hn₀ we get (hyp : P n₀)
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
