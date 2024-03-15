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
  suggestionsProviders : Array Name := #[]
  anonymousLemmas : Array Name := #[]
  anonymousSplitLemmas : Array Name := #[]
  unfoldableDefs : Array Name := #[]

-- we do not use `deriving Inhabited` because we want to control the default value.
instance : Inhabited VerboseConfiguration := ⟨{}⟩

instance : ToString VerboseConfiguration where
  toString conf := s!"Language: {conf.lang}\nSuggestions providers: {conf.suggestionsProviders}" ++
    "\nAnonymous lemmas: {conf.anonymousLemmas}\nAnonymous split lemmas: {conf.anonymousSplitLemmas}"

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

variable {m: Type → Type} [Monad m] [MonadEnv m] {α : Type} [Inhabited α]

def Verbose.setSuggestionsProviders (suggestionsProviders : Array Name) : m Unit := do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders := suggestionsProviders}

def Verbose.getLang : m String := do
  return toString (← verboseConfigurationExt.get).lang

elab "#print_verbose_config" : command => do
  let conf ← verboseConfigurationExt.get
  IO.println conf

open Elab Term Meta Command

elab "configureSuggestionProviders" args:ident* : command => do
  let providers ← suggestionsProviderListsExt.gatherNames args (some <| .const `SuggestionProvider [])
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders := providers}

elab "configureAnonymousLemmas" args:ident* : command => do
  let lemmas ← anonymousFactSplittingLemmasListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousLemmas := lemmas}

elab "configureAnonymousSplitLemmas" args:ident* : command => do
  let lemmas ← anonymousGoalSplittingListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousSplitLemmas := lemmas}

elab "configureUnfoldableDefs" args:ident* : command => do
  let defs ← unfoldableDefsListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with unfoldableDefs := defs}

elab "setLang" lang:ident : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with lang := lang.getId}
