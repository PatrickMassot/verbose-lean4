import Verbose.Infrastructure.DeclListExtension
import Verbose.Infrastructure.SingleValPersistentEnvExtension
import Verbose.Infrastructure.WidgetM
import Verbose.Infrastructure.SelectionInfo

/-! # Environment extensions

This file defines the various environment extensions that allow to configure Verbose Lean.
This does not include the extension keeping track of multilingual functions that has its own
file.
It includes a number of extensions that tracks lists of declaration names, as well as the main
configuration extension `verboseConfigurationExt`.
-/

open Lean Elab Command Term Meta


/-! ##  Suggestions provider lists extension -/

registerDeclListExtension suggestionsProviderListsExt

/-- Print all registered suggestions provider lists for debugging purposes. -/
elab "#suggestions_provider_lists" : command => do
  suggestionsProviderListsExt.printDeclList

/-- Register a list of suggestions providers. -/
elab doc:(Lean.Parser.Command.docComment)? "SuggestionProviderList" name:ident ":=" args:ident* : command =>
  suggestionsProviderListsExt.defineDeclList doc name args

abbrev SuggestionProvider := SelectionInfo → MVarId → WidgetM Unit

/-! ##  Anonymous goal splitting lemmas lists extension -/

registerDeclListExtension anonymousGoalSplittingListsExt

/-- Print all registered anonymous split lemmas lists for debugging purposes. -/
elab "#anonymous_goals_split_lemmas_lists" : command => do
  anonymousGoalSplittingListsExt.printDeclList

/-- Register a list of anonymous split lemmas. -/
elab doc:(Lean.Parser.Command.docComment)?
    "AnonymousGoalSplittingLemmasList" name:ident ":=" args:ident* : command =>
  anonymousGoalSplittingListsExt.defineDeclList doc name args

/-! ##  Anonymous fact splitting lemmas lists extension -/

registerDeclListExtension anonymousFactSplittingLemmasListsExt

/-- Print all registered anonymous lemmas lists for debugging purposes. -/
elab "#anonymous_fact_splitting_lemmas_lists" : command => do
  anonymousFactSplittingLemmasListsExt.printDeclList

/-- Register a list of anonymous lemmas. -/
elab doc:(Lean.Parser.Command.docComment)?
    "AnonymousFactSplittingLemmasList" name:ident ":=" args:ident* : command =>
  anonymousFactSplittingLemmasListsExt.defineDeclList doc name args

/-! ##  Unfoldable definitions lists extension -/

registerDeclListExtension unfoldableDefsListsExt

/-- Print all registered unfoldable definitions lists for debugging purposes. -/
elab "#unfoldable_defs_lists" : command => do
  unfoldableDefsListsExt.printDeclList

/-- Register a list of unfoldable definitions. -/
elab doc:(Lean.Parser.Command.docComment)? "UnfoldableDefsList" name:ident ":=" args:ident* : command =>
  unfoldableDefsListsExt.defineDeclList doc name args

/-! ## Verbose configuration -/

structure VerboseConfiguration where
  lang : Name := `en
  anonymousFactSplittingLemmas : Array Name := #[]
  anonymousGoalSplittingLemmas : Array Name := #[]
  unfoldableDefs : Array Name := #[]
  suggestionsProviders : Array Name := #[]
  dataProviders : HashMap Expr (Array Name):= ∅

-- we do not use `deriving Inhabited` because we want to control the default value.
instance : Inhabited VerboseConfiguration := ⟨{}⟩


initialize verboseConfigurationExt : SingleValPersistentEnvExtension VerboseConfiguration
  ← registerSingleValPersistentEnvExtension `gameExt VerboseConfiguration

open Elab Term Meta Command

def Verbose.getSuggestionsProviders : MetaM (Array SuggestionProvider) := do
  let conf ← verboseConfigurationExt.get
  let env ← getEnv
  let mut result : Array SuggestionProvider := #[]
  for name in conf.suggestionsProviders do
    if let some info := env.find? name then
      unless ← isDefEq info.type (.const `SuggestionProvider []) do
        throwError "The type {info.type} of {name} is not suitable: expected SuggestionProvider"
      result := result.push (← unsafe evalConst SuggestionProvider name)
    else
      throwError "Could not find declaration {name}"
  return result

abbrev DataProvider := Array Term → MetaM Term

def Verbose.getDataProviders : MetaM (HashMap Expr (Array DataProvider)) := do
  let conf ← verboseConfigurationExt.get
  let env ← getEnv
  let mut result : HashMap Expr (Array DataProvider) := ∅
  for (type, providerNames) in conf.dataProviders.toList do
    let mut providerFuns : Array (Array Term → MetaM Term) := #[]
    for providerName in providerNames do
      if let some info := env.find? providerName then
        unless ← isDefEq info.type (.const ``DataProvider []) do
          throwError "The type {info.type} of {providerName} is not suitable: expected DataProvider"
        providerFuns := providerFuns.push (← unsafe evalConst DataProvider providerName)
      else
        throwError "Could not find declaration {providerName}"
    result := result.insert type providerFuns
  return result

variable {m: Type → Type} [Monad m] [MonadEnv m] {α : Type} [Inhabited α]

def Verbose.setSuggestionsProviders (suggestionsProviders : Array Name) : m Unit := do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders}

def Verbose.getLang : m String := do
  return toString (← verboseConfigurationExt.get).lang

/-- Print the current Verbose Lean configuration, for debugging purposes. -/
elab "#print_verbose_config" : command => do
  let conf ← verboseConfigurationExt.get
  IO.println s!"Language: {conf.lang}\n\n\
     Anonymous fact splitting lemmas: {conf.anonymousFactSplittingLemmas}\n\n\
     Anonymous goal splitting lemmas: {conf.anonymousGoalSplittingLemmas}\n\n\
     Suggestions providers: {conf.suggestionsProviders}\n\nData providers:"
  for (type, providers) in conf.dataProviders.toList do
    IO.println s!"  {type}: {providers}"

open Elab Term Meta Command

elab "configureSuggestionProviders" args:ident* : command => do
  let suggestionsProviders ← suggestionsProviderListsExt.gatherNames args
    (some <| .const `SuggestionProvider [])
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders}

declare_syntax_cat providersDescr -- (behavior := symbol)
syntax providersField := term ": [" ident,* "]"
syntax "{" providersField,* "}" : providersDescr

def elabProvidersField : TSyntax `providersField → Term × Array Ident
| `(providersField|$x:term : [$[$idents],*]) => (x, idents)
| _  => default

def elabProvidersDescr : TSyntax `providersDescr → TermElabM (HashMap Expr (Array Name))
| `(providersDescr|{$[$fields],*}) => do
  let mut res := []
  for (x, names) in fields.map elabProvidersField do
    res := (← elabTerm x none, names.map (·.getId)) :: res
  return HashMap.ofList res
| _ => default

elab "configureDataProviders" args:providersDescr : command => do
  let conf ← verboseConfigurationExt.get
  let descr ← runTermElabM (fun _ ↦ elabProvidersDescr args)
  verboseConfigurationExt.set {conf with dataProviders := descr}

elab "configureAnonymousFactSplittingLemmas" args:ident* : command => do
  let lemmas ← anonymousFactSplittingLemmasListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousFactSplittingLemmas := lemmas}

elab "configureAnonymousGoalSplittingLemmas" args:ident* : command => do
  let lemmas ← anonymousGoalSplittingListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousGoalSplittingLemmas := lemmas}

elab "configureUnfoldableDefs" args:ident* : command => do
  let defs ← unfoldableDefsListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with unfoldableDefs := defs}

elab "setLang" lang:ident : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with lang := lang.getId}
