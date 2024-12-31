import Lean

open Lean Elab Command Term Meta
open Lean.Parser.Command (docComment)

/-! ## Declaration names extensions infrastructure -/

abbrev NameListDict := RBMap Name (List Name) Name.quickCmp

abbrev DeclListExtension := SimplePersistentEnvExtension (Name × List Name) NameListDict

def mkDeclListDeclName (name : Name) : Name := `DeclListExtensions ++ name

structure DeclsListExtension

def DeclListExtension.defineDeclList (ext : DeclListExtension) (doc : Option (TSyntax ``docComment))
    (name : Ident) (args : Array Ident) : CommandElabM Unit := do
  let env ← getEnv
  let sets := ext.getState env
  if sets.contains name.getId then
    throwError "There is already a declaration list named {name}."
  let mut entries : List Name := []
  for arg in args do
    try
      let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo arg
      entries := entries.insert name
    catch _ =>
      if let some set := sets.find? arg.getId then
        addConstInfo arg (mkDeclListDeclName arg.getId)
        entries := entries ++ set
      else
        throwError "Could not find a declaration or declaration list named {arg}."
  let declName :=  name.getId
  let name' := mkDeclListDeclName declName
  elabCommand (← `(command| $[$doc]? def $(mkIdentFrom name <| `_root_ ++ name') :
    DeclsListExtension := {}))
  modifyEnv (ext.addEntry · (declName, entries))


macro "registerDeclListExtension" name:ident : command =>
`(initialize $name : DeclListExtension ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map ⟨key, val⟩ ↦ map.insert key val
    addImportedFn := fun as ↦ .fromArray (as.flatMap id) Name.quickCmp
  })

def  DeclListExtension.printDeclList (ext : DeclListExtension) : CommandElabM Unit :=
  for entry in ext.getState (← getEnv) do
    IO.println s!"{entry.1} : {entry.2}"

def DeclListExtension.gatherNames (ext : DeclListExtension) (args : Array Ident)
    (expectedType? : Option Expr := none) : CommandElabM (Array Name) := do
  let mut result : Array Name := #[]
  let env ← getEnv
  let sets := ext.getState env
  have checkName (ident : Ident) : CommandElabM (Option Name) := do
    let name ← try
        liftCoreM <| realizeGlobalConstNoOverloadWithInfo ident
      catch _ => return none
    if let some info := env.find? name then
      if let some expectedType := expectedType? then
        unless ← liftTermElabM <| isDefEq info.type expectedType do
          let expectedFmt ← liftTermElabM <| ppExpr expectedType
          throwError "The type {info.type} of {name} is not suitable: expected {expectedFmt}"
      return name
    else
      return none
  for arg in args do
    if let some name ← checkName arg then
      result := result.push name
    else if let some set := sets.find? arg.getId then
      addConstInfo arg (mkDeclListDeclName arg.getId)
      for name in set do
        if let some name ← checkName (mkIdent name) then
          result := result.push name
        else
          throwError "Could not find a declaration or declaration list named {name}."
    else
      throwError "Could not find a declaration or declaration list named {arg}."
  return result
