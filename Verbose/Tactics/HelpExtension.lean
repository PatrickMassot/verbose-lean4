import Verbose.Tactics.Help

open Lean Meta Elab Tactic Term Verbose

/-- An extension for `positivity`. -/
structure HelpExt where
  run (goal : MVarId) (hyp : Name) (hypId : Ident) (hypType : Expr) : SuggestionM Unit

/-- Read a `help` extension from a declaration of the right type. -/
def mkHelpExt (n : Name) : ImportM HelpExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck HelpExt opts ``HelpExt n

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

/-- Each `help` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev HelpEntry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `help` declarations -/
initialize helpExt : PersistentEnvExtension HelpEntry (HelpEntry × HelpExt)
    (List HelpEntry × DiscrTree HelpExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq HelpExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v discrTreeConfig) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkHelpExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

/-- Attribute for identifying `help` extensions. -/
syntax (name := Verbose.help) "help " term,+ : attr

initialize registerBuiltinAttribute {
  name := `help
  descr := "adds a help extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| help $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'help', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'help', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkHelpExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx => do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e discrTreeConfig
      setEnv <| helpExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}
