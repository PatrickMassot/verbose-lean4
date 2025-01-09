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

open Lean hiding HashMap
open Std Elab Command Term Meta
open Lean.Parser.Command (docComment)

/-! ## Help provider lists extension

This is used by the help tactic.
-/

registerDeclListExtension helpProviderListsExt

/-- Print all registered help provider lists for debugging purposes. -/
elab "#help_provider_lists" : command => do
  helpProviderListsExt.printDeclList

/-- Register a list of help providers for the suggestions widget. -/
elab doc:(docComment)? "HelpProviderList" name:ident ":=" args:ident* : command =>
  helpProviderListsExt.defineDeclList doc name args

/-! ##  Suggestions provider lists extension -/

registerDeclListExtension suggestionsProviderListsExt

/-- Print all registered suggestions provider lists for debugging purposes. -/
elab "#suggestions_provider_lists" : command => do
  suggestionsProviderListsExt.printDeclList

/-- Register a list of suggestions providers. -/
elab doc:(docComment)? "SuggestionProviderList" name:ident ":=" args:ident* : command =>
  suggestionsProviderListsExt.defineDeclList doc name args

abbrev SuggestionProvider := SelectionInfo → MVarId → WidgetM Unit

/-! ## Data provider lists extension

This is used by the suggestions widget.
-/

registerDeclListExtension dataProviderListsExt

/-- Print all registered data provider lists for debugging purposes. -/
elab "#data_provider_lists" : command => do
  dataProviderListsExt.printDeclList

/-- Register a list of data providers for the suggestions widget. -/
elab doc:(docComment)? "DataProviderList" name:ident ":=" args:ident* : command =>
  dataProviderListsExt.defineDeclList doc name args

/-! ##  Anonymous goal splitting lemmas lists extension -/

registerDeclListExtension anonymousGoalSplittingListsExt

/-- Print all registered anonymous split lemmas lists for debugging purposes. -/
elab "#anonymous_goal_splitting_lemmas_lists" : command => do
  anonymousGoalSplittingListsExt.printDeclList

/-- Register a list of anonymous split lemmas. -/
elab doc:(docComment)?
    "AnonymousGoalSplittingLemmasList" name:ident ":=" args:ident* : command =>
  anonymousGoalSplittingListsExt.defineDeclList doc name args

/-! ##  Anonymous fact splitting lemmas lists extension -/

registerDeclListExtension anonymousFactSplittingLemmasListsExt

/-- Print all registered anonymous lemmas lists for debugging purposes. -/
elab "#anonymous_fact_splitting_lemmas_lists" : command => do
  anonymousFactSplittingLemmasListsExt.printDeclList

/-- Register a list of anonymous lemmas. -/
elab doc:(docComment)?
    "AnonymousFactSplittingLemmasList" name:ident ":=" args:ident* : command =>
  anonymousFactSplittingLemmasListsExt.defineDeclList doc name args

/-! ##  Anonymous case splitting lemmas lists extension -/

registerDeclListExtension anonymousCaseSplittingListsExt

/-- Print all registered anonymous case split lemmas lists for debugging purposes. -/
elab "#anonymous_case_splitting_lemmas_lists" : command => do
  anonymousCaseSplittingListsExt.printDeclList

/-- Register a list of anonymous case split lemmas. -/
elab doc:(docComment)?
    "AnonymousCaseSplittingLemmasList" name:ident ":=" args:ident* : command =>
  anonymousCaseSplittingListsExt.defineDeclList doc name args

/-! ##  Unfoldable definitions lists extension -/

registerDeclListExtension unfoldableDefsListsExt

/-- Print all registered unfoldable definitions lists for debugging purposes. -/
elab "#unfoldable_defs_lists" : command => do
  unfoldableDefsListsExt.printDeclList

/-- Register a list of unfoldable definitions. -/
elab doc:(docComment)? "UnfoldableDefsList" name:ident ":=" args:ident* : command =>
  unfoldableDefsListsExt.defineDeclList doc name args

/-! ## Verbose configuration -/

structure VerboseConfiguration where
  lang : Name := `en
  anonymousFactSplittingLemmas : Array Name := #[]
  anonymousGoalSplittingLemmas : Array Name := #[]
  anonymousCaseSplittingLemmas : Array Name := #[]
  unfoldableDefs : Array Name := #[]
  suggestionsProviders : Array Name := #[]
  dataProviders : HashMap Expr (Array Name):= ∅
  helpProviders : Array Name := #[]
  useHelpTactic : Bool := true
  suggestsUnfolding : Bool := true
  useSuggestionWidget : Bool := true
  debugSuggestionWidget : Bool := false
  allowNegationByContradiction : Bool := false

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

declare_syntax_cat providersDescr
syntax providersField := term " : " "[" ident,* "]"
syntax "{" providersField,* "}" : providersDescr

def elabProvidersField : TSyntax `providersField → Term × Array Ident
| `(providersField|$x:term :[$[$idents],*]) => (x, idents)
| _  => default

def elabProvidersDescr : TSyntax `providersDescr → CommandElabM (HashMap Expr (Array Name))
| `(providersDescr|{$[$fields],*}) => do
  let mut res := []
  for (x, names) in fields.map elabProvidersField do
    res := (← runTermElabM fun _ ↦ elabTerm x none, ← dataProviderListsExt.gatherNames names) :: res
  return HashMap.ofList res
| _ => default

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
     Use help tactic: {conf.useHelpTactic}\n\n\
     Suggest unfolding: {conf.suggestsUnfolding}\n\n\
     Use suggestion widget: {conf.useSuggestionWidget}\n\n\
     Debug suggestion widget: {conf.debugSuggestionWidget}\n\n\
     Allow proving negations by contradiction: {conf.allowNegationByContradiction}\n\n\
     Anonymous fact splitting lemmas: {conf.anonymousFactSplittingLemmas}\n\n\
     Anonymous goal splitting lemmas: {conf.anonymousGoalSplittingLemmas}\n\n\
     Anonymous case splitting lemmas: {conf.anonymousCaseSplittingLemmas}\n\n\
     Help providers: {conf.helpProviders}\n\n\
     Suggestions providers: {conf.suggestionsProviders}\n\nData providers:"
  for (type, providers) in conf.dataProviders.toList do
    IO.println s!"  {type}: {providers}"

elab "configureHelpProviders" args:ident* : command => do
  let helpProviders ← helpProviderListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with helpProviders}

elab "configureSuggestionProviders" args:ident* : command => do
  let suggestionsProviders ← suggestionsProviderListsExt.gatherNames args
    (some <| .const `SuggestionProvider [])
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders}

elab "configureDataProviders" args:providersDescr : command => do
  let conf ← verboseConfigurationExt.get
  let descr ← elabProvidersDescr args
  verboseConfigurationExt.set {conf with dataProviders := descr}

elab "configureAnonymousFactSplittingLemmas" args:ident* : command => do
  let lemmas ← anonymousFactSplittingLemmasListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousFactSplittingLemmas := lemmas}

elab "configureAnonymousGoalSplittingLemmas" args:ident* : command => do
  let lemmas ← anonymousGoalSplittingListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousGoalSplittingLemmas := lemmas}

elab "configureAnonymousCaseSplittingLemmas" args:ident* : command => do
  let lemmas ← anonymousCaseSplittingListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousCaseSplittingLemmas := lemmas}

elab "configureUnfoldableDefs" args:ident* : command => do
  let defs ← unfoldableDefsListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with unfoldableDefs := defs}

elab "setLang" lang:ident : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with lang := lang.getId}

elab "enableUnfoldingSuggestions" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestsUnfolding := true}

elab "disableUnfoldingSuggestions" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestsUnfolding := false}

elab "enableHelpTactic" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with useHelpTactic := true}

elab "disableHelpTactic" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with useHelpTactic := false}

elab "enableWidget" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with useSuggestionWidget := true}

elab "disableWidget" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with useSuggestionWidget := false}

elab "debugWidget" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with debugSuggestionWidget := true}

elab "allowProvingNegationsByContradiction" : command => do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with allowNegationByContradiction := true}
