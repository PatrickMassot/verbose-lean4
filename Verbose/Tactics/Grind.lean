/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

/-!
# Strict grind wrapper for Verbose Lean

This file provides `grind_strict`, a wrapper around the `grind` tactic that only uses
explicitly specified local hypotheses. This is useful in educational contexts where
students should provide explicit justifications for their reasoning steps.

## Usage

```lean
-- Only use hypotheses h1 and h2, plus theorem foo
grind_strict [h1, h2, foo]
```

The tactic will:
1. Identify which arguments are names of local hypotheses
2. Clear all local hypotheses except those specified (and their forward dependencies)
3. Call `grind only [...]` with any non-hypothesis arguments (theorems, lemmas, etc.)
-/

open Lean Elab Tactic Meta

namespace Verbose.Tactics

/-- Collect all FVarIds that the given FVarIds depend on (forward dependencies).
    If hypothesis `h2 : P h1` depends on `h1`, and we want to keep `h2`,
    we must also keep `h1`. -/
private def collectDependencies (lctx : LocalContext) (keepFVars : Array FVarId) : MetaM (Array FVarId) := do
  let mut result := keepFVars
  let mut changed := true
  -- Fixed point iteration to collect all dependencies
  while changed do
    changed := false
    for decl in lctx do
      if result.contains decl.fvarId then continue
      -- Check if any hypothesis we're keeping depends on this one
      for keepId in result do
        if let some keepDecl := lctx.find? keepId then
          if keepDecl.type.containsFVar decl.fvarId then
            result := result.push decl.fvarId
            changed := true
            break
          if let some val := keepDecl.value? then
            if val.containsFVar decl.fvarId then
              result := result.push decl.fvarId
              changed := true
              break
  return result

/-- Implementation of grind_strict.
    Takes identifiers, separates them into local hypotheses and other terms,
    clears unwanted hypotheses, and calls grind only with the term arguments. -/
def grindStrictImpl (args : Array (TSyntax `ident)) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    -- Separate arguments into local hypothesis names and other (theorem) names
    let lctx ← getLCtx
    let mut hypFVars : Array FVarId := #[]
    let mut otherArgs : Array (TSyntax `ident) := #[]

    for arg in args do
      let name := arg.getId
      -- Check if this name refers to a local hypothesis
      if let some decl := lctx.findFromUserName? name then
        hypFVars := hypFVars.push decl.fvarId
      else
        -- It's not a local hypothesis, so it should be a theorem/lemma name
        otherArgs := otherArgs.push arg

    -- Collect dependencies of the hypotheses we want to keep
    let keepFVars ← collectDependencies lctx hypFVars

    -- Get all local hypothesis FVarIds (excluding implementation details)
    let allFVars := lctx.decls.toArray.filterMap fun decl? =>
      decl?.bind fun decl =>
        if decl.isImplementationDetail then none else some decl.fvarId

    -- Collect FVarIds to clear (those not in the keep set)
    -- Preserve typeclass instances so grind can use them
    let fvarsToClear := allFVars.filter fun fvar =>
      !keepFVars.contains fvar &&
      !(lctx.find? fvar |>.map (·.binderInfo == .instImplicit) |>.getD false)

    -- Use tryClearMany' which handles ordering and returns the new goal
    let (newGoal, _) ← goal.tryClearMany' fvarsToClear

    replaceMainGoal [newGoal]

    -- Collect all extra theorem names to pass to grind only
    let mut allArgs := otherArgs

    -- Always include le_of_eq theorems so grind can handle ≤/≥ goals from equalities
    allArgs := allArgs.push (mkIdent `Lean.Grind.Order.le_of_eq_1)
    allArgs := allArgs.push (mkIdent `Lean.Grind.Order.le_of_eq_2)

    -- Build and run the grind tactic
    if allArgs.isEmpty then
      evalTactic (← `(tactic| grind only))
    else
      let paramStxs ← allArgs.mapM fun id => `(Parser.Tactic.grindParam| $id:ident)
      evalTactic (← `(tactic| grind only [$paramStxs,*]))

/-- `grind_strict [h1, h2, thm]` is a wrapper around `grind only` that:
    1. Clears all local hypotheses except those explicitly listed (h1, h2, etc.)
    2. Passes any non-hypothesis names (theorems, lemmas) to `grind only [...]`

    This is useful in educational contexts where students should explicitly
    provide justifications for their reasoning, preventing `grind` from
    automatically using assumptions that weren't explicitly mentioned.

    Example:
    ```lean
    example (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = c := by
      -- Only uses h1 and h2, ignores h3
      grind_strict [h1, h2]
    ```
-/
syntax "grind_strict" "[" ident,* "]" : tactic

elab_rules : tactic
  | `(tactic| grind_strict [$args,*]) => grindStrictImpl args.getElems

end Verbose.Tactics

section Test
open Verbose.Tactics
variable {α : Type} (a b c d : α)

-- Test 1: Provided hypotheses are available
example (h1 : a = b) (h2 : b = c) (_h3 : c = d) : a = c := by
  grind_strict [h1, h2]

-- Test 2: Non-provided hypotheses are NOT available
example (h1 : a = b) (_h2 : b = c) (h3 : c = d) : a = d := by
  fail_if_success grind_strict [h1, h3]
  grind

-- Test 3: Non-hypothesis arguments are passed to grind only
-- Define a custom opaque predicate that grind can't derive on its own
opaque myPred : Nat → Prop
axiom myPred_two : myPred 2

-- Without the lemma, grind can't solve this
example : myPred 2 := by
  fail_if_success grind_strict []
  grind_strict [myPred_two]

-- Test 4: Mix of hypotheses and theorems
example (h : a = b) : a = b ∧ myPred 2 := by
  constructor
  · grind_strict [h]
  · fail_if_success grind_strict []
    grind_strict [myPred_two]

example (h : a = b) : a = b ∧ myPred 2 := by
  fail_if_success grind_strict []
  fail_if_success grind_strict [h]
  fail_if_success grind_strict [myPred_two]
  grind_strict [h, myPred_two]

example [LE α] [Std.IsPreorder α] (h1 : a = b) (h2 : b = c) (_h3 : c = d) : a ≤ c := by
  grind_strict [h1, h2]


end Test
