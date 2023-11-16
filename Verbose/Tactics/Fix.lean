import Lean
import Std.Tactic.RCases
import Mathlib.Data.Set.Basic

import Verbose.Tactics.Common

open Lean Meta Elab Tactic

inductive intro_rel where
| lt | gt | le | ge | mem
deriving Repr

inductive introduced where
| typed (syn : Syntax) (n : Name) (e : Syntax) : introduced
| bare (syn : Syntax) (n : Name) : introduced
| related (syn : Syntax) (n : Name) (rel : intro_rel) (e : Syntax) : introduced
deriving Repr


/- Like Lean.Meta.intro except it introduces only data and fails on Prop.
It takes the current goal id as `mvarId` and a name for the newly introduced object
and returns a `FVarId` referring the newly introduced object and a `MVarId` for the new
goal.
 -/
def introObj (mvarId : MVarId) (name : Name) : MetaM (FVarId × MVarId) := do
  let tgt ← whnf (← mvarId.getType)
  if tgt.isForall ∨ tgt.isLet then
    let (fvar, newmvarId) ← mvarId.intro name
    newmvarId.withContext do
      let t := (← fvar.getDecl).type
      if (← inferType t).isProp then
        throwError "There is no object to introduce here."
      else
        pure (fvar, newmvarId)
  else
    throwError "There is no object to introduce here."

/- Like Lean.Meta.intro except it introduces only assumptions and fails on data.
It takes the current goal id as `mvarId` and a name for the newly introduced object
and returns a `FVarId` referring the newly introduced object and a `MVarId` for the new
goal.
 -/
def introHyp (mvarId : MVarId) (name : Name) : MetaM (FVarId × MVarId) := do
  let tgt ← whnf (← mvarId.getType)
  if tgt.isForall ∨ tgt.isLet then
    let (fvar, newmvarId) ← mvarId.intro name
    newmvarId.withContext do
      let t := (← fvar.getDecl).type
      if (← inferType t).isProp then
        pure (fvar, newmvarId)
      else
        throwError "There is no assumption to introduce here."
  else
    throwError "There is no assumption to introduce here."

def Fix1 : introduced → TacticM Unit
| introduced.typed syn n t   =>  do
  withRef syn do
    checkName n
    -- Introduce n, getting the corresponding FVarId and the new goal MVarId with its context
    let (n_fvar, new_goal) ← introObj (← getMainGoal) n
    -- Change the default MVarContext to the newly created one for the benefit of `elabTerm`
    new_goal.withContext do
      replaceMainGoal [← new_goal.changeLocalDecl n_fvar (← elabTerm t none)]
| introduced.bare syn n      => do
  withRef syn do
    checkName n
    -- Introduce n, forget the corresponding FVarId and get the new goal MVarId with its context
    let (_, new_goal) ← introObj (← getMainGoal) n
    replaceMainGoal [new_goal]
| introduced.related syn n rel e => do
  withRef syn do
    checkName n
    let (n_fvar, new_goal) ← introObj (← getMainGoal) n
    new_goal.withContext do
      let n_decl ← getLocalDeclFromUserName n
      let n_type := n_decl.type
      -- Let's build the RHS e as an expr. In the membership case we don't have extra information
      -- in other case we elaborate knowing we should get the same type as n
      let (E : Expr) ← match rel with
              | intro_rel.mem => elabTerm e none
              | _ => elabTerm e n_type
      -- Now create a name for the relation assumption that will be created
      let (hyp_name : String) := if e matches `(0) then
                        match rel with
                        | intro_rel.lt  => n.toString ++ "_neg"
                        | intro_rel.gt  => n.toString ++ "_pos"
                        | intro_rel.le  => n.toString ++ "_neg"
                        | intro_rel.ge  => n.toString ++ "_pos"
                        | intro_rel.mem => "h_" ++ n.toString -- shouldn't happen

                      else
                        match rel with
                        | intro_rel.lt  => n.toString ++ "_lt"
                        | intro_rel.gt  => n.toString ++ "_gt"
                        | intro_rel.le  => n.toString ++ "_le"
                        | intro_rel.ge  => n.toString ++ "_ge"
                        | intro_rel.mem => n.toString ++ "_mem"

      let n_expr : Expr := mkFVar n_fvar
      let (rel_expr : Expr) ← match rel with
                    | intro_rel.lt => mkAppM ``LT.lt #[n_expr, E]
                    | intro_rel.gt => mkAppM ``GT.gt #[n_expr, E]
                    | intro_rel.le => mkAppM ``LE.le #[n_expr, E]
                    | intro_rel.ge => mkAppM ``GE.ge #[n_expr, E]
                    | intro_rel.mem => mkAppM ``Membership.mem #[n_expr, E]

      let (hyp_fvar, newer_goal) ← new_goal.intro hyp_name
      newer_goal.withContext do
        let new_mvarid ← newer_goal.changeLocalDecl hyp_fvar rel_expr
        replaceMainGoal [new_mvarid]

def Assume1 : introduced → TacticM Unit
| introduced.typed syn n t   =>  do
  withRef syn do
    checkName n
    -- Introduce n, getting the corresponding FVarId and the new goal MVarId with its context
    let (n_fvar, new_goal) ← introHyp (← getMainGoal) n
    -- Change the default MVarContext to the newly created one for the benefit of `elabTerm`
    new_goal.withContext do
      replaceMainGoal [← new_goal.changeLocalDecl n_fvar (← elabTerm t none)]
| introduced.bare syn n      => do
  withRef syn do
    checkName n
    -- Introduce n, forget the corresponding FVarId and get the new goal MVarId with its context
    let (_, new_goal) ← introHyp (← getMainGoal) n
    replaceMainGoal [new_goal]
| introduced.related .. => pure ()


open Lean Elab

declare_syntax_cat fixDecl
syntax ident : fixDecl
syntax ident ":" term : fixDecl
syntax ident "<" term : fixDecl
syntax ident ">" term : fixDecl
syntax ident ("<=" <|> "≤") term : fixDecl
syntax ident (">=" <|> "≥") term : fixDecl
syntax ident "∈" term : fixDecl
syntax "(" fixDecl ")" : fixDecl

declare_syntax_cat assumeDecl
syntax ident : assumeDecl
syntax ident ":" term : assumeDecl
syntax "(" assumeDecl ")" : assumeDecl

open Mathlib Tactic PushNeg in
/-- Execute main loop of `push_neg` at a local hypothesis and return the new FVarId and new goal. -/
def pushNegLocalDecl' (goal : MVarId) (fvarId : FVarId) : MetaM (FVarId × MVarId) := goal.withContext do
  let ldecl ← fvarId.getDecl
  let tgt ← instantiateMVars ldecl.type
  let myres ← pushNegCore tgt
  let some (newFvarId, newGoal) ← applySimpResultToLocalDecl goal fvarId myres False | failure
  return (newFvarId, newGoal)

open Mathlib Tactic PushNeg in
def forContradiction (n : Name) (e : Option Term) : TacticM Unit := withMainContext do
  checkName n
  evalApplyLikeTactic MVarId.apply <| ← `(Classical.byContradiction)

  let (new_hyp, new_goal) ← introHyp (← getMainGoal) n
  new_goal.withContext do
  match e with
  | some stmt => do
      let stmt_expr ← elabTerm stmt none
      let new_hyp_type_expr ← new_hyp.getType
      if (← isDefEq stmt_expr new_hyp_type_expr) then
        replaceMainGoal [new_goal]
      else
        let ((newFvar, newGoal) : FVarId × MVarId) ← pushNegLocalDecl' new_goal new_hyp
        newGoal.withContext do
        let new_hyp_type_expr ← newFvar.getType
        unless (← isDefEq stmt_expr new_hyp_type_expr) do
          throwError "This is not what you should assume for contradiction, even after pushing negations."
        replaceMainGoal [newGoal]
  | none => pushNegLocalDecl new_hyp <|> replaceMainGoal [new_goal]
