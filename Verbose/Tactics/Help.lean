import Verbose.Infrastructure.Multilingual
import Verbose.Infrastructure.HelpInfrastructure
import Verbose.Tactics.Common
import Verbose.Tactics.Fix

/-! # The help tactic

-/

open Lean Meta Elab Tactic Verbose

/-! ## Help at goal -/

register_endpoint helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit

@[hypHelp _ ∧ _]
def helpConjunction : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .conjunction _ propo propo':= hypType then
    let h₁N ← goal.getUnusedUserName `h
    let h₁I := mkIdent h₁N
    let h₂N ← goal.getUnusedUserName `h'
    let h₂I := mkIdent h₂N
    let p₁S ← propo.delab
    let p₂S ← propo'.delab
    helpConjunctionSuggestion hyp h₁I h₂I p₁S p₂S

register_endpoint helpSinceConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit

@[hypHelp _ ∧ _]
def helpSinceConjunction : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .conjunction _ propo propo':= hypType then
    let h₁N ← goal.getUnusedUserName `h
    let h₁I := mkIdent h₁N
    let h₂N ← goal.getUnusedUserName `h'
    let h₂I := mkIdent h₂N
    let p₁S ← propo.delab
    let p₂S ← propo'.delab
    helpConjunctionSuggestion hyp h₁I h₂I p₁S p₂S

register_endpoint helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit

@[hypHelp _ ∨ _]
def helpDisjunction : HypHelpExt where
  run (_goal : MVarId) (hyp : Name) (_hypType : VExpr) : SuggestionM Unit :=
    helpDisjunctionSuggestion hyp

register_endpoint helpSinceDisjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) : SuggestionM Unit

@[hypHelp _ ∨ _]
def helpSinceDisjunction : HypHelpExt where
  run (_goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .disjunction _ propo propo':= hypType then
    let p₁S ← propo.delab
    let p₂S ← propo'.delab
    helpSinceDisjunctionSuggestion hyp p₁S p₂S

register_endpoint helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit

@[hypHelp _ → _]
def helpImplication : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .impl _ le re _lhs _rhs:= hypType then
    let HN ← goal.getUnusedUserName `H
    let H'N ← goal.getUnusedUserName `H'
    let closes ← re.closesGoal goal
    helpImplicationSuggestion hyp HN H'N closes le re

register_endpoint helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit

@[hypHelp _ ↔ _]
def helpEquivalence : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .iff _ le re _lhs _rhs:= hypType then
    let hyp'N ← goal.getUnusedUserName `hyp
    helpEquivalenceSuggestion hyp hyp'N le re

register_endpoint helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : Expr) : SuggestionM Unit

@[hypHelp _ = _]
def helpEqual : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    let decl := ← getLocalDeclFromUserName hyp
      if let .equal _ le re:= hypType then
    let hyp' ← goal.getUnusedUserName `hyp
    let closes ← decl.toExpr.linarithClosesGoal goal
    helpEqualSuggestion hyp hyp' closes le re

register_endpoint helpSinceEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : Expr)
  (leS reS goalS : Term) : SuggestionM Unit

@[hypHelp _ = _]
def helpSinceEqual : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    let decl := ← getLocalDeclFromUserName hyp
      if let .equal _ le re:= hypType then
    let hyp' ← goal.getUnusedUserName `hyp
    let closes ← decl.toExpr.linarithClosesGoal goal
    let leS ← PrettyPrinter.delab le
    let reS ← PrettyPrinter.delab re
    let goalS ← PrettyPrinter.delab (← goal.getType)
    helpSinceEqualSuggestion hyp hyp' closes le re leS reS goalS

register_endpoint helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit

@[hypHelp _ ≤ _, _ < _, _ ≥ _, _ > _]
def helpIneq : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    let closes ← (← getLocalDeclFromUserName hyp).toExpr.linarithClosesGoal goal
      if let .ineq _ _le _rel _re:= hypType then
    helpIneqSuggestion hyp closes

register_endpoint helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) : SuggestionM Unit

register_endpoint helpMemUnionSuggestion (hyp : Name) : SuggestionM Unit

register_endpoint helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit

@[hypHelp _ ∈ _]
def helpMem : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
  if let .mem _ elem set:= hypType then
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

register_endpoint helpContradictionSuggestion (hypId : Ident) : SuggestionM Unit

@[hypHelp False]
def helpFalse : HypHelpExt where
  run (_goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
  if let .prop (.const `False _):= hypType then
  helpContradictionSuggestion hyp.ident

register_endpoint helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit

@[hypHelp _ ⊆ _]
def helpSubset : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
  if let .subset _ lhs rhs:= hypType then
  let ambientTypeE := (← instantiateMVars (← inferType lhs)).getAppArgs[0]!
  let ambientTypePP ← ppExpr ambientTypeE
  let l ← ppExpr lhs
  let xN ← goal.getUnusedUserName `x
  let hxN ← goal.getUnusedUserName `hx
  let hx'N ← goal.getUnusedUserName `hx'
  helpSubsetSuggestion hyp xN hxN hx'N rhs l ambientTypePP

register_endpoint helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
  (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident)
  (ineqS p'S : Term) : SuggestionM Unit

register_endpoint helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
  (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit

register_endpoint helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name) (headDescr n₀rel : String) (t : Format)
  (newsI : Ident) (pS : Term) : SuggestionM Unit

@[hypHelp ∀ _, _ → _]
def helpForallRel : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
  if let .forall_rel _ var_name typ rel rel_rhs propo := hypType then
    let py ← ppExpr rel_rhs
    let t ← ppExpr typ
    let n₀ ← goal.getUnusedUserName (Name.mkSimple s!"{var_name}₀")
    let hn₀N ← goal.getUnusedUserName (Name.mkSimple s!"h{n₀}")
    withRenamedFVar var_name n₀ do
    match propo with
    | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
      let var_name' := ← goal.getUnusedUserName var_name'
      let ineqIdent := mkIdent <| .mkSimple s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
      let ineqS ← mkRelStx var_name' rel' rel_rhs'
      let hn'S := mkIdent <| .mkSimple s!"h{var_name'}"
      let p'S ← propo'.delab
      let headDescr := s!"∀ {var_name}{rel}{py}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ..."
      let hypDescr := s!"{n₀}{rel}{py}"
      helpForAllRelExistsRelSuggestion hyp var_name' n₀ hn₀N headDescr hypDescr t hn'S
        ineqIdent ineqS p'S
    | .exist_simple _e' var_name' _typ' propo' => do
      let n' := ← goal.getUnusedUserName var_name'
      let hn' := Name.mkSimple s!"h{var_name'}"
      let p'S ← propo'.delab
      let headDescr := s!"∀ {var_name}{rel}{py}, ∃ {var_name'}, ..."
      let n₀rel := s!"{n₀}{rel}{py}"
      helpForAllRelExistsSimpleSuggestion hyp n' hn' n₀ hn₀N headDescr n₀rel t p'S
    | _ => do
      let newsI := (← goal.getUnusedUserName `hyp).ident
      let pS ← propo.delab
      let headDescr := s!"∀ {var_name}{rel}{py}, ..."
      let n₀rel := s!"{n₀}{rel}{py}"
      helpForAllRelGenericSuggestion hyp n₀ hn₀N headDescr n₀rel t newsI pS

register_endpoint helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name) (headDescr : String)
   (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) : SuggestionM Unit

register_endpoint helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
  (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit

register_endpoint helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
  (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit

register_endpoint helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String) (t : Format)
    (pS : Term) : SuggestionM Unit

register_endpoint helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format): SuggestionM Unit

@[hypHelp ∀ _, _]
def helpForallSimple : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
  if let .forall_simple _ var_name typ propo := hypType then
    let decl := ← getLocalDeclFromUserName hyp
    let t ← ppExpr typ
    let n := toString var_name
    let n₀ := n ++ "₀"
    let nn₀ ← goal.getUnusedUserName (.mkSimple n₀)
    let hn₀ ← goal.getUnusedUserName (.mkSimple <| "h" ++ n₀)
    withRenamedFVar var_name nn₀ do
    match propo with
    | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
      let var_name' ← goal.getUnusedUserName var_name'
      let ineqIdent := mkIdent <| .mkSimple s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
      let ineqS ← mkRelStx var_name' rel' rel_rhs'
      let hn'S := mkIdent <| .mkSimple s!"h{var_name'}"
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

register_endpoint helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit

@[hypHelp ∃ _, _ ∧ _]
def helpExistsRel : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .exist_rel _ var_name _typ rel rel_rhs propo := hypType then
    let y ← ppExpr rel_rhs
    let name ← goal.getUnusedUserName var_name
    let nameS := mkIdent name
    let hS := mkIdent <| .mkSimple s!"h{name}"
    let ineqName := Name.mkSimple s!"{name}{symb_to_hyp rel rel_rhs}"
    let ineqIdent := mkIdent ineqName
    let ineqS ← mkRelStx name rel rel_rhs
    withRenamedFVar var_name name do
    let pS ← propo.delab
    helpExistRelSuggestion hyp s!"∃ {var_name}{rel}{y}, ..." nameS ineqIdent hS ineqS pS

register_endpoint helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String) (pS : Term) :
  SuggestionM Unit

@[hypHelp ∃ _, _]
def helpExistsSimple : HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .exist_simple _ var_name _typ propo := hypType then
    let n ← goal.getUnusedUserName var_name
    let hn := Name.mkSimple s!"h{n}"
    withRenamedFVar var_name n do
    let pS ← propo.delab
    let headDescr := s!"∃ {var_name}, ..."
    helpExistsSimpleSuggestion hyp n hn headDescr pS

register_endpoint helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit

@[hypHelp ∀ _, _]
def helpData : HypHelpExt where
  run (_goal : MVarId) (hyp : Name) (hypType : VExpr) : SuggestionM Unit := do
    if let .data e := hypType then
    let t ← ppExpr e
    helpDataSuggestion hyp t

HelpProviderList DefaultHypHelp :=
  helpData
  helpExistsSimple
  helpExistsRel
  helpForallSimple
  helpForallRel
  helpSubset
  helpFalse
  helpMem
  helpIneq
  helpEqual
  helpEquivalence
  helpImplication
  helpDisjunction
  helpConjunction

register_endpoint assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit

register_endpoint assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) : SuggestionM Unit

register_endpoint helpNothingSuggestion : SuggestionM Unit

def helpAtHyp (goal : MVarId) (hyp : Name) : SuggestionM Unit :=
  goal.withContext do
  let config ← verboseConfigurationExt.get
  let decl := ← getLocalDeclFromUserName hyp
  let hypId := mkIdent hyp
  if ← decl.type.closesGoal goal then
    assumptionClosesSuggestion hypId
    return
  let mut hypType ← instantiateMVars decl.type
  if config.suggestsUnfolding then
    if ← hypType.isAppFnUnfoldable then
      if let some expandedHypType ← hypType.expandHeadFun then
        let expandedHypTypeS ← PrettyPrinter.delab expandedHypType
        assumptionUnfoldingSuggestion hypId expandedHypTypeS
        hypType := expandedHypType
  parse hypType fun m ↦ do
    for ext in ← (hypHelpExt.getState (← getEnv)).2.getMatch hypType do
      try
        if config.helpProviders.contains ext.name then
          ext.run goal hyp m
          flush
      catch _ =>
        pure ()
    if (← get).suggestions.isEmpty then
      helpNothingSuggestion


/-! ## Help at goal -/

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal starts with “{headDescr}”"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal has shape “{headDescr}”"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Hence a direct proof starts with:"

register_endpoint helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) : SuggestionM Unit

@[goalHelp _ ⊆ _]
def helpSubsetGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .subset _e lhs rhs := g then
    let l ← ppExpr lhs
    let r ← ppExpr rhs
    let lT ← PrettyPrinter.delab lhs
    let xN ← goal.getUnusedUserName `x
    helpSubsetGoalSuggestion l r xN lT

register_endpoint helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) : SuggestionM Unit

@[goalHelp ∀ _, _ → _]
def helpForallRelGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .forall_rel _e var_name _typ rel rel_rhs _propo := g then
        let py ← ppExpr rel_rhs
        let n ← goal.getUnusedUserName var_name
        let ineqS ← mkFixDeclIneq n rel rel_rhs
        let headDescr := s!"∀ {var_name}{rel}{py}"
        helpFixSuggestion headDescr ineqS

@[goalHelp ∀ _, _]
def helpForallSimpleGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .forall_simple _e var_name typ _propo := g then
        let t ← ppExpr typ
        let n ← goal.getUnusedUserName var_name
        let declS ← mkFixDecl n typ
        let headDescr := s!"∀ {var_name} : {t},"
        helpFixSuggestion headDescr declS

register_endpoint helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
  (fullTgtS : Term) : SuggestionM Unit

@[goalHelp ∃ _, _ ∧ _]
def helpExistsRelGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .exist_rel _e var_name typ rel rel_rhs propo := g then
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        withRenamedFVar var_name nn₀ do
        let ineqS ← mkRelStx nn₀ rel rel_rhs
        let tgtS ← propo.delab
        let fullTgtS ← `($ineqS ∧ $tgtS)
        let t ← ppExpr typ
        let headDescr := s!"∃ {n}{rel}{← ppExpr rel_rhs}, ..."
        helpExistsRelGoalSuggestion headDescr nn₀ t fullTgtS


register_endpoint helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
  (tgt : Term) : SuggestionM Unit

@[goalHelp ∃ _, _]
def helpExistsSimpleGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .exist_simple _e var_name typ propo := g then
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        withRenamedFVar var_name nn₀ do
        let tgt ← propo.delab
        let t ← ppExpr typ
        let headDescr := s!"∃ {n}, ..."
        helpExistsGoalSuggestion headDescr nn₀ t tgt

register_endpoint helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit

@[goalHelp _ ∧ _]
def helpConjunctionGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .conjunction _e propo propo' := g then
        let p ← propo.delab
        let p' ← propo'.delab
        helpConjunctionGoalSuggestion p p'

register_endpoint helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit

@[goalHelp _ ∨ _]
def helpDisjunctionGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .disjunction _e propo propo' := g then
        let p ← propo.delab
        let p' ← propo'.delab
        helpDisjunctionGoalSuggestion p p'

register_endpoint helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name) (leStx : Term) :
  SuggestionM Unit

@[goalHelp _ → _]
def helpImplicationGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .impl _e le _re lhs _rhs := g then
        let l ← le.fmt
        let leStx ← lhs.delab
        let Hyp ← goal.getUnusedUserName `hyp
        let headDescr := s!"{l} ⇒ ..."
        helpImplicationGoalSuggestion headDescr Hyp leStx

register_endpoint helpContraposeGoalSuggestion : SuggestionM Unit

@[goalHelp _ → _]
def helpContraposeGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .impl .. := g then
        helpContraposeGoalSuggestion

register_endpoint helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit

def Lean.Expr.isNegation (e : Expr) : Bool :=
  e.isAppOf' `Not || e.isAppOf' `Ne

open Mathlib.Tactic.PushNeg in
@[goalHelp _]
def helpByContradictionGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    unless (← verboseConfigurationExt.get).allowNegationByContradiction do
      let .prop tgt := g | pure ()
      if tgt.isNegation then return
    let neg : Expr := .app (.const ``Not []) g.toExpr
    goal.withContext do
    let pushed := (← pushNegCore neg).expr
    let Hyp := mkIdent (← goal.getUnusedUserName `hyp)
    helpByContradictionSuggestion Hyp (← PrettyPrinter.delab pushed)

register_endpoint helpNegationGoalSuggestion (hyp : Ident) (g : Format) (assum : Term) : SuggestionM Unit

@[goalHelp ¬ _]
def helpNegationGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .prop (.app (.const `Not ..) pE) := g then
      let p ← ppExpr pE
      let pS ← PrettyPrinter.delab pE
      let Hyp := mkIdent (← goal.getUnusedUserName `hyp)
      helpNegationGoalSuggestion Hyp p pS

register_endpoint helpNeGoalSuggestion (l r : Format) (lS rS : Term) (Hyp : Ident) : SuggestionM Unit

@[goalHelp _ ≠ _]
def helpNeGoal : GoalHelpExt where
  run (goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .prop (mkAppN (.const `Ne ..) #[_, lE, rE]) := g then
      let l ← ppExpr lE
      let r ← ppExpr rE
      let lS ← PrettyPrinter.delab lE
      let rS ← PrettyPrinter.delab rE
      let Hyp := mkIdent (← goal.getUnusedUserName `hyp)
      helpNeGoalSuggestion l r lS rS Hyp


register_endpoint helpEquivalenceGoalSuggestion (r l : Format) (rS lS : Term) : SuggestionM Unit

@[goalHelp _ ↔ _]
def helpEquivalenceGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .iff _e le re lhs rhs := g then
        let l ← le.fmt
        let lS ← lhs.delab
        let r ← re.fmt
        let rS ← rhs.delab
        helpEquivalenceGoalSuggestion r l rS lS

register_endpoint helpSetEqSuggestion (l r : Format) (lS rS : Term) : SuggestionM Unit

register_endpoint helpEqGoalSuggestion (l r : Format) : SuggestionM Unit

@[goalHelp _ = _]
def helpEqualGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .equal _e le re := g then
        let ambiantTypeE ← instantiateMVars (← inferType le)
        let l ← ppExpr le
        let lS ← PrettyPrinter.delab le
        let r ← ppExpr re
        let rS ← PrettyPrinter.delab re
        if ambiantTypeE.isApp && ambiantTypeE.isAppOf `Set then
          helpSetEqSuggestion l r lS rS
        else
          helpEqGoalSuggestion l r

register_endpoint helpIneqGoalSuggestion (l r : Format) (rel : String) : SuggestionM Unit

@[goalHelp  _ ≤ _, _ < _, _ ≥ _, _ > _]
def helpIneqGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .ineq _e le rel re := g then
        let l ← ppExpr le
        let r ← ppExpr re
        helpIneqGoalSuggestion l r rel

register_endpoint helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit

register_endpoint helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit

register_endpoint helpNoIdeaGoalSuggestion : SuggestionM Unit

@[goalHelp _ ∈ _]
def helpMemGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .mem _ elem set := g then
      if let some (le, _) := set.memInterPieces? then
        helpMemInterGoalSuggestion elem le
      else if let some (le, re) := set.memUnionPieces? then
        helpMemUnionGoalSuggestion elem le re
      else
        helpNoIdeaGoalSuggestion

register_endpoint helpFalseGoalSuggestion : SuggestionM Unit

@[goalHelp False]
def helpFalseGoal : GoalHelpExt where
  run (_goal : MVarId) (g : VExpr) : SuggestionM Unit := do
    if let .prop (.const `False _) := g then
        helpFalseGoalSuggestion

register_endpoint helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) : SuggestionM Unit

register_endpoint helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit

register_endpoint helpNothingGoalSuggestion : SuggestionM Unit

def helpAtGoal (goal : MVarId) : SuggestionM Unit :=
  goal.withContext do
  let config ← verboseConfigurationExt.get
  let mut goalType ← instantiateMVars (← goal.getType)
  if ← goalType.isAppFnUnfoldable then
    if let some expandedGoalType ← goalType.expandHeadFun then
      let expandedGoalTypeS ← PrettyPrinter.delab expandedGoalType
      helpUnfoldableGoalSuggestion expandedGoalTypeS
      goalType := expandedGoalType
  if goalType.getAppFn matches .const `goalBlocker .. then
    let actualGoal := goalType.getAppArgs[0]!
    helpAnnounceGoalSuggestion (← actualGoal.stx)
    return
  parse goalType fun g ↦ do
    for ext in ← (goalHelpExt.getState (← getEnv)).2.getMatch goalType do
      try
        if config.helpProviders.contains ext.name then
          ext.run goal g
          flush
      catch _ =>
        pure ()
    if (← get).suggestions.isEmpty then
      helpNothingGoalSuggestion

HelpProviderList SinceGoalHelp :=
  helpSinceConjunction
  helpSinceDisjunction

HelpProviderList DefaultGoalHelp :=
  helpFalseGoal
  helpMemGoal
  helpIneqGoal
  helpEqualGoal
  helpEquivalenceGoal
  helpImplicationGoal
  helpDisjunctionGoal
  helpConjunctionGoal
  helpExistsSimpleGoal
  helpExistsRelGoal
  helpForallSimpleGoal
  helpForallRelGoal
  helpSubsetGoal
  helpNeGoal
  helpNegationGoal

configureHelpProviders DefaultHypHelp DefaultGoalHelp



/-- English comma separated lists. The `oxford` argument controls whether to include an Oxford comma. -/
def commaSep (s : Array String) (conj : String := "and") (sep : String := ", ") (ifEmpty : String := "") (oxford : Bool := false) : String :=
  match s.size with
    | 0 => ifEmpty
    | 1 => s[0]!
    | 2 => s[0]! ++ " " ++ conj ++ " " ++ s[1]!
    | _ => String.intercalate sep (s.extract 0 (s.size - 1)).toList ++ (if oxford then sep else " ") ++ conj ++ " " ++ s[s.size - 1]!
