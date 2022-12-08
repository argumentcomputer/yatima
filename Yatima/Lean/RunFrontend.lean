/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Yatima.Lean.Preprocess

namespace Yatima
open Lean Elab 

private def ensureExtensionsArraySize (env : Environment) : IO Environment :=
  EnvExtensionInterfaceImp.ensureExtensionsSize env

private def mkInitialExtensionStates : IO (Array EnvExtensionState) := EnvExtensionInterfaceImp.mkInitialExtStates

/--
Construct a mapping from persistent extension name to entension index at the array of persistent extensions.
We only consider extensions starting with index `>= startingAt`.
-/
private def mkExtNameMap (startingAt : Nat) : IO (HashMap Name Nat) := do
  let descrs ← persistentEnvExtensionsRef.get
  let mut result := {}
  for h : i in [startingAt : descrs.size] do
    have : i < descrs.size := h.upper
    let descr := descrs[i]
    result := result.insert descr.name i
  return result

private def setImportedEntries (env : Environment) (mods : Array ModuleData) (startingAt : Nat := 0) : IO Environment := do
  let mut env := env
  let extDescrs ← persistentEnvExtensionsRef.get
  /- For extensions starting at `startingAt`, ensure their `importedEntries` array have size `mods.size`. -/
  for extDescr in extDescrs[startingAt:] do
    env := extDescr.toEnvExtension.modifyState env fun s => { s with importedEntries := mkArray mods.size #[] }
  /- For each module `mod`, and `mod.entries`, if the extension name is one of the extensions after `startingAt`, set `entries` -/
  let extNameIdx ← mkExtNameMap startingAt
  for h : modIdx in [:mods.size] do
    have : modIdx < mods.size := h.upper
    let mod := mods[modIdx]
    for (extName, entries) in mod.entries do
      if let some entryIdx := extNameIdx.find? extName then
        env := extDescrs[entryIdx]!.toEnvExtension.modifyState env fun s => { s with importedEntries := s.importedEntries.set! modIdx entries }
  return env

private partial def finalizePersistentExtensions (env : Environment) (mods : Array ModuleData) (opts : Options) : IO Environment := do
  loop 0 env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    -- Recall that the size of the array stored `persistentEnvExtensionRef` may increase when we import user-defined environment extensions.
    let pExtDescrs ← persistentEnvExtensionsRef.get
    if i < pExtDescrs.size then do
      let extDescr := pExtDescrs[i]!
      -- IO.println s!">> finalizePersistentExtensions, extDescr: {extDescr.name}"
      if extDescr.name == `Lean.Compiler.specExtension then
        return ← loop (i + 1) env -- LMAO??
      let s := extDescr.toEnvExtension.getState env
      let prevSize := (← persistentEnvExtensionsRef.get).size
      let prevAttrSize ← getNumBuiltiAttributes
      let newState ← extDescr.addImportedFn s.importedEntries { env := env, opts := opts }
      let mut env := extDescr.toEnvExtension.setState env { s with state := newState }
      env ← ensureExtensionsArraySize env
      if (← persistentEnvExtensionsRef.get).size > prevSize || (← getNumBuiltiAttributes) > prevAttrSize then
        -- This branch is executed when `pExtDescrs[i]` is the extension associated with the `init` attribute, and
        -- a user-defined persistent extension is imported.
        -- Thus, we invoke `setImportedEntries` to update the array `importedEntries` with the entries for the new extensions.
        env ← setImportedEntries env mods prevSize
        -- See comment at `updateEnvAttributesRef`
        env ← updateEnvAttributes env
      loop (i + 1) env
    else
      return env

partial def importModules (imports : List Import) (opts : Options) (trustLevel : UInt32 := 0) : IO Environment := profileitIO "import" opts do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    let (_, s) ← importMods imports |>.run {}
    let mut numConsts := 0
    for mod in s.moduleData do
      numConsts := numConsts + mod.constants.size + mod.extraConstNames.size
    let mut modIdx : Nat := 0
    let mut const2ModIdx : HashMap Name ModuleIdx := mkHashMap (capacity := numConsts)
    let mut constantMap : HashMap Name ConstantInfo := mkHashMap (capacity := numConsts)
    for mod in s.moduleData do
      for cname in mod.constNames, cinfo in mod.constants do
        match constantMap.insert' cname cinfo with
        | (constantMap', replaced) =>
          constantMap := constantMap'
          if replaced then
            throwAlreadyImported s const2ModIdx modIdx cname
        const2ModIdx := const2ModIdx.insert cname modIdx
      for cname in mod.extraConstNames do
        const2ModIdx := const2ModIdx.insert cname modIdx
      modIdx := modIdx + 1
    let constants : ConstMap := SMap.fromHashMap constantMap false
    let exts ← mkInitialExtensionStates
    let env : Environment := {
      const2ModIdx    := const2ModIdx
      constants       := constants
      extraConstNames := {}
      extensions      := exts
      header          := {
        quotInit     := !imports.isEmpty -- We assume `core.lean` initializes quotient module
        trustLevel   := trustLevel
        imports      := imports.toArray
        regions      := s.regions
        moduleNames  := s.moduleNames
        moduleData   := s.moduleData
      }
    }
    let specializeAttrs := Compiler.specExtension.getState env |>.specInfo
    IO.println s!"specializeAttrs before: {specializeAttrs.contains ``List.map}"
    let env ← setImportedEntries env s.moduleData
    let env ← finalizePersistentExtensions env s.moduleData opts
    let specializeAttrs := Compiler.specExtension.getState env |>.specInfo
    IO.println s!"specializeAttrs after: {specializeAttrs.contains ``List.map}"
    pure env
where
  importMods : List Import → StateRefT ImportState IO Unit
  | []    => pure ()
  | i::is => do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      importMods is
    else do
      modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
      let mFile ← findOLean i.module
      unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
      let (mod, region) ← readModuleData mFile
      importMods mod.imports.toList
      modify fun s => { s with
        moduleData  := s.moduleData.push mod
        regions     := s.regions.push region
        moduleNames := s.moduleNames.push i.module
      }
      importMods is

def headerToImports (header : Syntax) : List Import :=
  let imports := if header[0].isNone then [{ module := `Init : Import }] else []
  imports ++ header[1].getArgs.toList.map fun stx =>
    -- `stx` is of the form `(Module.import "import" "runtime"? id)
    let runtime := !stx[1].isNone
    let id      := stx[2].getId
    { module := id, runtimeOnly := runtime }

def processHeader (header : Syntax) (opts : Options) (messages : MessageLog) (inputCtx : Parser.InputContext) (trustLevel : UInt32 := 0)
    : IO (Environment × MessageLog) := do
  try
    let env ← importModules (headerToImports header) opts trustLevel
    IO.println ">> processHeader"
    IO.println s!"`List.map exists? {(Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt `List.map).isSome}"
    let specializeAttrs := Compiler.specExtension.getState env |>.specInfo
    IO.println s!"specializeAttrs: {specializeAttrs.toList.map Prod.fst}"
    pure (env, messages)
  catch e =>
    let env ← mkEmptyEnvironment
    let spos := header.getPos?.getD 0
    let pos  := inputCtx.fileMap.toPosition spos
    pure (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos := pos })

end Yatima