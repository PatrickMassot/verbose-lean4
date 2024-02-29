import Lean
import Verbose.Tactics.WidgetM
import Verbose.Tactics.SelectionInfo

open Lean

instance : ToString NameSet :=
  ⟨fun n ↦ n.toList.map toString |> toString⟩

/-- A persistent environment extension that is meant to hold a single (mutable) value. -/
def SingleValPersistentEnvExtension (α : Type) := PersistentEnvExtension α α α

instance {α} [Inhabited α] : Inhabited (SingleValPersistentEnvExtension α) :=
  inferInstanceAs <| Inhabited  <| PersistentEnvExtension α α α

def registerSingleValPersistentEnvExtension (name : Name) (α : Type) [Inhabited α] : IO (SingleValPersistentEnvExtension α) :=
  registerPersistentEnvExtension {
    name            := name,
    mkInitial       := pure default,
    addImportedFn   := mkStateFromImportedEntries (fun _ b => return b) (return default),
    addEntryFn      := (λ _ b => b),
    exportEntriesFn := λ x => #[x]
  }

variable {m: Type → Type} [Monad m] [MonadEnv m] {α : Type} [Inhabited α]

def SingleValPersistentEnvExtension.get (ext : SingleValPersistentEnvExtension α) : m α :=
  return ext.getState (← getEnv)

def SingleValPersistentEnvExtension.set (ext : SingleValPersistentEnvExtension α) (a : α) : m Unit := do
  modifyEnv (ext.modifyState · (λ _ => a))
abbrev NameSetDict := RBMap Name NameSet Name.quickCmp

/-- Environment extension for suggestions providers sets. -/
initialize suggestionsProviderSetsExt : SimplePersistentEnvExtension (Name × NameSet) NameSetDict ←
  registerSimplePersistentEnvExtension {
    name := `suggestionsExt
    addEntryFn := fun map ⟨key, val⟩ ↦ map.insert key val
    addImportedFn := fun as ↦ .fromArray (as.concatMap id) Name.quickCmp
  }

open Elab Command in
/-- Print all registered suggestions provider sets for debugging purposes. -/
elab "#suggestions_provider_sets" : command => do
  for entry in suggestionsProviderSetsExt.getState (← getEnv) do
    dbg_trace "{entry.1} : {entry.2}"

elab "SuggestionProviderSet" name:ident ":=" args:ident* : command => do
  let env ← getEnv
  let sets := suggestionsProviderSetsExt.getState env
  if sets.contains name.getId then
    throwError "There is already a suggestions provider set named {name}."
  let mut entries : NameSet := ∅
  for arg in args do
    let argN := arg.getId
    if (env.find? argN).isSome then
      entries := entries.insert argN
    else if let some set := sets.find? argN then
      entries := entries ++ set
    else
      throwError "Could not find a declaration or suggestions provider set named {argN}."
  modifyEnv (suggestionsProviderSetsExt.addEntry · (name.getId, entries))

abbrev SuggestionProvider := SelectionInfo → MVarId → WidgetM Unit

structure VerboseConfiguration where
  lang : Name := `en
  suggestionsProviders : Array (Name × SuggestionProvider)
  deriving Inhabited

instance : ToString VerboseConfiguration where
  toString conf := s!"Language: {conf.lang}\nSuggestions providers: {conf.suggestionsProviders.map Prod.fst}"

initialize verboseConfigurationExt : SingleValPersistentEnvExtension VerboseConfiguration ← registerSingleValPersistentEnvExtension `gameExt VerboseConfiguration

def Verbose.getSuggestionsProviders : m (Array SuggestionProvider) := do
  let conf ← verboseConfigurationExt.get
  return conf.suggestionsProviders.map Prod.snd

def Verbose.setSuggestionsProviders (suggestionsProviders : Array (Name × SuggestionProvider)) : m Unit := do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders := suggestionsProviders}

elab "#print_verbose_config" : command => do
  let conf ← verboseConfigurationExt.get
  IO.println conf

open Elab Term

elab "configureSuggestionProviders" args:ident* : command => do
  let mut providers : Array (Name × SuggestionProvider) := #[]
  let env ← getEnv
  let sets := suggestionsProviderSetsExt.getState env
  let getFun name : Command.CommandElabM (Option SuggestionProvider) := do
    if let some info := env.find? name then
      unless info.type.isConstOf `SuggestionProvider do
        throwError "The type {info.type} of {name} is not suitable: expected SuggestionProvider"
      return some (← unsafe evalConst SuggestionProvider name)
    else
      return none
  for arg in args do
    let argN := arg.getId
    if let some provider ← getFun argN then
      providers := providers.push (argN, provider)
    else if let some set := sets.find? argN then
      for name in set do
        if let some provider ← getFun name then
          providers := providers.push (name, provider)
        else
          throwError "Could not find a declaration or suggestions provider set named {name}."
    else
      throwError "Could not find a declaration or suggestions provider set named {argN}."
  Verbose.setSuggestionsProviders providers
