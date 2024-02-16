import Verbose.Tactics.Help

open Lean Meta Elab Tactic Term Verbose

structure HypHelpExt where
  run (goal : MVarId) (hyp : Name) (hypType : Expr) : SuggestionM Unit

/-- Read a `help` extension from a declaration of the right type. -/
def mkHypHelpExt (n : Name) : ImportM HypHelpExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck HypHelpExt opts ``HypHelpExt n

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

/-- Each `help` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev HypHelpEntry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `help` declarations -/
initialize hypHelpExt : PersistentEnvExtension HypHelpEntry (HypHelpEntry × HypHelpExt)
    (List HypHelpEntry × DiscrTree HypHelpExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq HypHelpExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v discrTreeConfig) dt
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
syntax (name := Verbose.hypHelp) "hypHelp " term,+ : attr

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
        DiscrTree.mkPath e discrTreeConfig
      setEnv <| hypHelpExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}

structure GoalHelpExt where
  run (goal : MVarId) (goalMExpr : MyExpr) : SuggestionM Unit

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
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v discrTreeConfig) dt
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
syntax (name := Verbose.goalHelp) "goalHelp " term,+ : attr

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
        DiscrTree.mkPath e discrTreeConfig
      setEnv <| goalHelpExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}
