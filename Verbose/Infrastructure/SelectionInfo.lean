import Lean
import Batteries.Lean.Expr

/-! # SelectionInfo infrastructure

The first piece of infrastructure needed by the suggestion widget is a way to reorganize the
selection information.
When user select subexpressions in the InfoView, Lean core provides a list of subexpressions
where each item mentions whether the subexpression is a goal or the name of a local context item
or inside the type of such an item or inside the value of such an item.

The `SelectionInfo` data structure is presenting the same information but from another
perspective, grouping the selections by kind instead of providing a flat list where
each item has a kind information. The function that turns such a list into a `SelectionInfo`
is `mkSelectionInfos` (more precisly it produces a `HashMap` of those indexed by the goals
`MVarId`s). Then a number of function consume this data to answer
various questions about what is selected.

-/

open Lean Meta Std

/-! ## SelectionInfo -/

structure SelectionInfo where
  /-- Whether the full goal is selected. -/
  fullGoal : Bool := false
  /-- Subexpressions selected in the goal.
  Not including the root subexpression whose presence is recorded in the `fullGoal` field. -/
  goalSubExprs : Array SubExpr.Pos := ∅
  /-- Selected data-carrying free variables. The key is a string representating the type. -/
  dataFVars : HashMap String (Array LocalDecl) := ∅
  /-- Selected data-carrying free variables. The key is a string representating the type.
  A free variable is considered selected if either its name or its full type is selected. -/
  propFVars : Array LocalDecl := ∅
  fVarsTypeSubExprs : HashMap FVarId (LocalDecl × Array SubExpr.Pos) := ∅
  fVarsValueSubExprs : HashMap FVarId (LocalDecl × Array SubExpr.Pos) := ∅
  selected : Array SubExpr.GoalsLocation
  deriving Inhabited

abbrev SelectionInfos := HashMap MVarId SelectionInfo

def mkSelectionInfos (selected : Array SubExpr.GoalsLocation) : MetaM SelectionInfos := do
  let mut res : SelectionInfos := ∅
  for ⟨goal, loc⟩ in selected do
    res ← goal.withContext do
      let ctx ← getLCtx
      match loc with
      | .hyp fvar => do
        let ld := ctx.get! fvar
        pushFVar ld res goal
      | .target pos =>
        if pos.isRoot then
          pure <| res.alter goal fun info? ↦
            match info? with
              | some info => some {info with fullGoal := true}
              | none => some {fullGoal := true, selected := selected}
        else
          pure <| res.alter goal fun info? ↦
            match info? with
              | some info => some {info with goalSubExprs := info.goalSubExprs.push pos}
              | none => some {goalSubExprs := #[pos], selected := selected}
      | .hypValue fvar pos =>
         let ld := ctx.get! fvar
         if pos.isRoot then
           pushFVar ld res goal
         else
           pure <| res.alter goal fun info? ↦
            match info? with
             | some info => some
               { info with
                 fVarsValueSubExprs := info.fVarsValueSubExprs.alter fvar fun x ↦
                   match x with
                   | some ⟨ld, epos⟩ => some (ld, epos.push pos)
                   | none => some (ld, #[pos]) }
             | none => some {fVarsValueSubExprs := HashMap.emptyWithCapacity.insert fvar (ld, #[pos]), selected := selected}
      | .hypType fvar pos =>
         let ld := ctx.get! fvar
         if pos.isRoot then
           pushFVar ld res goal
         else
           pure <| res.alter goal fun info? ↦
            match info? with
            | some info => some
                { info with
                  fVarsTypeSubExprs := info.fVarsTypeSubExprs.alter fvar fun x ↦ match x with
                                      | some ⟨ld, epos⟩ => some (ld, epos.push pos)
                                      | none => some (ld, #[pos]) }
            | none => some {fVarsTypeSubExprs := HashMap.emptyWithCapacity.insert fvar (ld, #[pos]), selected := selected}
  return res

  where pushFVar (ld : LocalDecl) (res : SelectionInfos) (goal : MVarId) := do
    if (← instantiateMVars (← inferType ld.type)).isProp then
      pure <| res.alter goal fun info? ↦ match info? with
        | some info => some {info with propFVars := info.propFVars.push ld}
        | none => some {propFVars := #[ld], selected := selected}
    else
      let typStr := toString (← ppExpr ld.type)
      pure <| res.alter goal fun info? ↦ match info? with
        | some info => some {info with
         dataFVars := info.dataFVars.alter typStr fun x ↦ match x with
          | some a => some (a.push ld)
          | none => some #[ld]}
        | none => some {dataFVars := HashMap.emptyWithCapacity.insert typStr #[ld], selected := selected}

def SelectionInfo.onlyGoal (si : SelectionInfo) : Bool :=
  si.dataFVars.isEmpty && si.propFVars.isEmpty && si.fVarsTypeSubExprs.isEmpty && si.fVarsValueSubExprs.isEmpty

def SelectionInfo.onlyFullGoal (si : SelectionInfo) : Bool := si.onlyGoal && si.fullGoal

def SelectionInfo.singleData (si : SelectionInfo) : Option LocalDecl :=
  if !si.fullGoal && si.goalSubExprs.isEmpty && si.propFVars.isEmpty && si.fVarsTypeSubExprs.isEmpty && si.fVarsValueSubExprs.isEmpty && si.dataFVars.size = 1 then
    some si.dataFVars.toList[0]!.2[0]!
  else
    none

def SelectionInfo.singleProp (si : SelectionInfo) : Option LocalDecl :=
  if !si.fullGoal && si.goalSubExprs.isEmpty && si.dataFVars.isEmpty && si.fVarsTypeSubExprs.isEmpty && si.fVarsValueSubExprs.isEmpty && si.propFVars.size = 1 then
    some si.propFVars[0]!
  else
    none

def SelectionInfo.onlyLocalDecls (si : SelectionInfo) : Bool :=
  !si.fullGoal && si.goalSubExprs.isEmpty

def SelectionInfo.forallFVars (si : SelectionInfo) : MetaM (Array LocalDecl) :=
  si.propFVars.filterM (fun fvar ↦ do return (←whnf fvar.type) matches .forallE ..)

def Lean.Expr.isExists (e : Expr) : Bool :=
  e.getAppFn' matches .const `Exists _

def SelectionInfo.simplePropFVars (si : SelectionInfo) : MetaM (Array LocalDecl) :=
  si.propFVars.filterM (fun fvar ↦ do let typ ← whnf fvar.type; return (!typ matches .forallE .. && !typ.isExists))
