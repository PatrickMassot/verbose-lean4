import Std.Util.TermUnsafe

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

unsafe def getEndpoint (key : Name) (α : Type) : CoreM (RBMap String α compare) := do
  return unsafeCast <| (endpointExt.getState (← getEnv)).2.findD key {}

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

class GetLanguage (β : Type) where
  run {α} (dflt : α) (get : CoreM (RBMap String α compare)) (eval : α → β) : β

@[inline, always_inline]
instance {β : Type} {γ : β → Type} [∀ b, GetLanguage (γ b)] :
    GetLanguage ((b : β) → γ b) where
  run dflt get eval b := GetLanguage.run dflt get (eval · b)

@[inline, always_inline]
instance {m β} [Monad m] [MonadLiftT CoreM m] [MonadOptions m] : GetLanguage (m β) where
  run dflt get eval := do
    let n ← get
    eval (n.findD (verbose.lang.get (← getOptions)) dflt)

syntax "endpoint " ident ppIndent(declSig) declVal : command
elab_rules : command
  | `(command| endpoint $key $sig $val) => do
    let sig ← match sig with
      | `(Parser.Command.declSig| $args* $ty:typeSpec) =>
        `(Parser.Command.optDeclSig| $args* $ty:typeSpec)
      | _ => pure ⟨.missing⟩
    let new := key.getId.modifyBase (· ++ `_default)
    Elab.Command.elabCommand <|← `(@[inline] def $(mkIdent new) $sig $val:declVal)
    let dflt ← mkDeclName new
    Elab.Command.elabCommand <|←
      `(def $key := GetLanguage.run $(mkCIdent dflt) (unsafe getEndpoint decl_name% _) id)

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
