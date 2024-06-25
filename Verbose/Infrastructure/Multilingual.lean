/- By Mario Carneiro. -/
import Mathlib.Tactic.TypeStar
import Verbose.Infrastructure.Extension

/-! # Multilingual functions infrastructure

This file sets up a multilingual functions framework. In order to define a multilingual function,
one must first register it using the `register_endpoint` command. This gives a function
that can immediately be used to define other functions. But running those functions
requires implementing the endpoint in the current language, which is `en` by default but
can be changed using `setLang`.

For instance:
```
open Lean

/-- Multilingual hello function. -/
register_endpoint hello : CoreM String

/-- Greeting function refering to our endpoint before any implementation is defined. -/
def greet (name : String) : CoreM String :=
  return (← hello) ++ " " ++ name

#eval greet "Patrick" -- throws error: no implementation of hello found for language en

implement_endpoint (lang := en) hello : CoreM String := pure "Hello"

implement_endpoint (lang := fr) hello : CoreM String := pure "Bonjour"

#eval greet "Patrick" -- returns "Hello Patrick"

setLang fr

#eval greet "Patrick" -- returns "Bonjour Patrick"
```

Note that above example creates three declarations: `hello`, `hello.en` and `hello.fr`, but
only the first one is explicitly used.

See the docstrings for implementation information, especially the docstring of `endpointExt`.
-/

namespace Verbose
open Lean Parser Command

/-- Dummy type that will act as placeholder for the type of all multilingual
functions. We could use anything in `Type` here, including `Nat` or `Empty`,
without altering the normal functioning of the multilingual framework,
but this would lead to potential crashes in case users directly define something
with this type. -/
opaque Endpoint : Type

/-- Make an endpoint implementation for key `key` from a concrete declaration name `decl`.
Checks that the type of `decl` matches the one that was declared for the `key` endpoint
so that users know immediately if they got the type wrong. Then forcefully evaluate
the declaration with type `Endpoint` and return the result. See the docstring of
`endpointExt` below for explanations about why we want that.
-/
def mkEndpoint (decl k : Name) : ImportM Endpoint := do
  let { env, opts, .. } ← read
  -- We now check the types matches in order to immediately tell users
  -- users if their implementation have the wrong type
  -- (this has nothing to do with Lean soundness since endpoint only run
  -- in monads anyway).
  let some info := env.find? decl
    | throw <| .userError ("unknown constant '" ++ toString decl ++ "'")
  let some info' := env.find? k
    | throw <| .userError ("unknown constant '" ++ toString decl ++ "'")
  unless info.type.eqv info'.type do
    throw <| .userError s!"\
      endpoint creation failed, type mismatch\n\
      expected: {info'.type}\n\
      provided: {info.type}"
  IO.ofExcept <| unsafe env.evalConst Endpoint opts decl

/-- The entries that are stored in olean files for the multilingual extension.
There is one entry per implementation of an endpoint. -/
structure Entry where
  /-- The implementation language. -/
  lang : String
  /-- The endpoint name. -/
  key : Name
  /-- The implementation declaration name. -/
  decl : Name

/-- Multilingual endpoints extension.

The data stored in olean files are arrays of `Entry`. But the state of this extension, as available
to users and their code, is a list of entries together with a map whose keys are endpoint names and
whose values are maps whose keys are strings describing languages and whose values are
the corresponding implementations, but represented by the dummy `Endpoint` type.

Note that the outer map is morally a dependent map. The type of values of the inner map
is always `Endpoint` but this is a placeholder: the actual endpoints types depend on
`key`.

When constructing the extension state from imported files (in `addImportedFn` here) and when adding
an entry (in the `implement_endpoint` command later), each implementation is forcefully turned into
a `Endpoint` by the `mkEndpoint` function which uses `Lean.Environment.evalConst` (after checking
that the implementation type is the one announced at registration time).

The actual type is equally forcefully restored using `unsafeCast` at calling time by the declaration
created by the `register_endpoint` command. This declaration is the user facing one.
Each `register_endpoint` also secretely creates a declaration, whose name is suffixed with the
language name, but it is only called by the user facing one, through the base intance of the
`GetLanguage` class below.
-/
initialize endpointExt :
    PersistentEnvExtension Entry (Entry × Endpoint)
      (List Entry × RBMap Name (RBMap String Endpoint compare) Name.quickCmp) ←
  let insert map key lang v := map.insert key <| map.findD key {} |>.insert lang v
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let map ← s.foldlM (init := {}) fun map s => s.foldlM (init := map) fun map e => do
        pure <| insert map e.key e.lang (← mkEndpoint e.decl e.key)
      pure ([], map)
    addEntryFn := fun (entries, s) (e, val) => (e :: entries, insert s e.key e.lang val)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

/-- Get the implementations map for the given endpoint key. This map
has language strings such as "en" as keys and values with type `Endpoint`. -/
def getEndpoint (key : Name) : CoreM (RBMap String Endpoint compare) := do
  return (endpointExt.getState (← getEnv)).2.findD key {}

-- extracted from Lean.Elab.mkDeclName
/-- Build a parsed hygienic name from the given name using the current macro scope
and the current namespace (also check that the given name is not `_root_` since this
makes sense only as a prefix). -/
def mkDeclName {m} [Monad m] [MonadResolveName m] [MonadError m] (name : Name) : m Name := do
  let currNamespace ← getCurrNamespace
  let view := extractMacroScopes name
  let name := view.name
  let isRootName := (`_root_).isPrefixOf name
  if name == `_root_ then
    throwError "invalid declaration name `_root_`, \
      `_root_` is a prefix used to refer to the 'root' namespace"
  return if isRootName then
    { view with name := name.replacePrefix `_root_ Name.anonymous }.review
  else currNamespace ++ name

/-- `GetLanguage β` records a way to turn any endpoint key and function
`eval : Endpoint → β` into an element of `β`. In practice this function will
be `unsafeCast` turning the placeholder `Endpoint` into the actual type of
the endpoint. -/
class GetLanguage (β : Sort*) where
  run (key : Name) (eval : Endpoint → β) : β

/-- The base instance for the `GetLanguage` class. Its `run` function retrieves the current language,
searches for the declaration corresponding to `key` in this language in the environment
and runs `eval` on it. -/
@[inline, always_inline]
instance {m β} [Monad m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : GetLanguage (m β) where
  run key eval := do
    let n ← getEndpoint key
    let lang ← Verbose.getLang
    let some val := n.find? lang | throwError "no implementation of {key} found for language {lang}"
    eval val

/-- Secondary instance for the `GetLanguage` class, on dependant functions when each target
type has an instance. Its `run` is the pointwise `run`. -/
@[inline, always_inline]
instance {β : Sort*} {γ : β → Sort*} [∀ b, GetLanguage (γ b)] : GetLanguage ((b : β) → γ b) where
  run key eval b := GetLanguage.run key (eval · b)

/-- Secondary instance for the `GetLanguage` class, on functions when the target
type has an instance. Its `run` is the pointwise `run`. Should be subsumed by the
dependent function instance, but type class synthesis struggle when piling up
too many of these. -/
@[inline, always_inline]
instance {β γ : Sort*} [GetLanguage γ] : GetLanguage (β → γ) where
  run key eval b := GetLanguage.run key (eval · b)

/-- Register a multilingual function. This function will instantly be usable to
define other functions, but running those will require actual implementating
for the current language. The final target type must be a monadic program
having access to the environment, for instance by running in `CoreM` or `MetaM`. -/
syntax (docComment)? "register_endpoint " ident ppIndent(declSig) : command
macro_rules
  | `(command| $[$doc]? register_endpoint $key $args* : $ty) => do
    `(set_option linter.unusedVariables false in
      def _cast : Endpoint → ∀ $args*, $ty := unsafe unsafeCast
      set_option linter.unusedVariables false in
      $[$doc]? def $key : ∀ $args*, $ty := @GetLanguage.run _ _ decl_name% _cast)

/-- Implement a multilingual function. The corresponding endpoint must
have been registered previously, with the same type. -/
syntax "implement_endpoint " "(" &"lang" " := " ident ") " ident ppIndent(declSig) declVal : command
elab_rules : command
  | `(command| implement_endpoint (lang := $lang) $key $sig $val) => do
    let sig ← match sig with
      | `(Parser.Command.declSig| $args* $ty:typeSpec) =>
        `(Parser.Command.optDeclSig| $args* $ty:typeSpec)
      | _ => pure ⟨.missing⟩
    let key ← Elab.Command.liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo key
    let decl := key ++ lang.getId
    Elab.Command.elabCommand <|← `(def $(mkIdent (`_root_ ++ decl)) $sig $val:declVal)
    unless ← MonadLog.hasErrors do
      let e ← Elab.Command.liftTermElabM (mkEndpoint decl key)
      let lang := lang.getId.toString
      modifyEnv (endpointExt.addEntry · ({ key, lang, decl }, e))

/-- For debugging purposes, list all endpoints that have at least one implementation.
Each one is listed with the list of languages currently implementing them.
You can indicate an endpoint identifier to list only its implementations. -/
elab "#list_implementations" key?:(ident)? : command => do
  let state := endpointExt.getState (← getEnv) |>.2
  match key? with
  | some key => match state.find? key.getId with
                | some map => IO.println s!"{map.toList.map Prod.fst}"
                | none => IO.println "No such endpoint or no implementation for it."
  | none => for (key, val) in state do
              IO.println s!"{key}: {val.toList.map Prod.fst}"
