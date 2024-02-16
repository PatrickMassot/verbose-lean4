import Std.Util.TermUnsafe
import Mathlib.Tactic.TypeStar

namespace Verbose
open Lean

opaque Endpoint : Type

def mkEndpoint (decl k : Name) : ImportM Endpoint := do
  let { env, opts, .. } ← read
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

structure Entry where
  lang : String
  key : Name
  decl : Name

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

def getEndpoint (key : Name) : CoreM (RBMap String Endpoint compare) := do
  return (endpointExt.getState (← getEnv)).2.findD key {}

-- extracted from Lean.Elab.mkDeclName
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

register_option verbose.lang : String := { defValue := "en" }

class GetLanguage (β : Sort*) where
  run (key : Name) (eval : Endpoint → β) : β

@[inline, always_inline]
instance {m β} [Monad m] [MonadLiftT CoreM m] [MonadOptions m] [MonadError m] : GetLanguage (m β) where
  run key eval := do
    let n ← getEndpoint key
    let lang := verbose.lang.get (← getOptions)
    let some val := n.find? lang | throwError "no endpoint declared for language {lang}"
    eval val

@[inline, always_inline]
instance {β : Sort*} {γ : β → Sort*} [∀ b, GetLanguage (γ b)] : GetLanguage ((b : β) → γ b) where
  run key eval b := GetLanguage.run key (eval · b)

@[inline, always_inline]
instance {β γ : Sort*} [GetLanguage γ] : GetLanguage (β → γ) where
  run key eval b := GetLanguage.run key (eval · b)

syntax "endpoint " ident ppIndent(declSig) : command
macro_rules
  | `(command| endpoint $key $args* : $ty) => do
    `(set_option linter.unusedVariables false in
      def _cast : Endpoint → ∀ $args*, $ty := unsafe unsafeCast
      set_option linter.unusedVariables false in
      def $key : ∀ $args*, $ty := @GetLanguage.run _ _ decl_name% _cast)

syntax "endpoint " "(" &"lang" " := " ident ") " ident ppIndent(declSig) declVal : command
elab_rules : command
  | `(command| endpoint (lang := $lang) $key $sig $val) => do
    let sig ← match sig with
      | `(Parser.Command.declSig| $args* $ty:typeSpec) =>
        `(Parser.Command.optDeclSig| $args* $ty:typeSpec)
      | _ => pure ⟨.missing⟩
    let key ← Elab.resolveGlobalConstNoOverloadWithInfo key
    let lang := lang.getId.toString
    let decl := key ++ lang
    Elab.Command.elabCommand <|← `(def $(mkIdent (`_root_ ++ decl)) $sig $val:declVal)
    unless ← MonadLog.hasErrors do
      let e ← Elab.Command.liftTermElabM (mkEndpoint decl key)
      modifyEnv (endpointExt.addEntry · ({ key, lang, decl }, e))
