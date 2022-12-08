import Lean.Compiler.LCNF.Main
import Yatima.Lean.Preprocess

namespace Lean.Compiler.LCNF

def getDeclsCore? (env : Environment) (ext : DeclExt) (declName : Name) : Array Decl :=
  match env.getModuleIdxFor? declName with
  | some modIdx => ext.getModuleEntries env modIdx
  | none        => 
    ext.getState env |>.foldl (init := #[]) fun acc _ decl => acc.push decl

def sanitizeName : Name → Name
  | .str name "_redArg" => name
  | x => x


namespace PassManager

deriving instance Repr for LitValue
deriving instance Repr for LCNF.Arg
deriving instance Repr for LetValue
deriving instance Repr for LetDecl
deriving instance Repr for Param
deriving instance Repr for FunDeclCore
deriving instance Repr for AltCore
deriving instance Repr for CasesCore
deriving instance Repr for Code
deriving instance Repr for InlineAttributeKind
deriving instance Repr for Decl

def runWithPasses (declNames : Array Name) (passes : Array Pass) (recurse? := true) : 
    CompilerM (Array Decl) := withAtLeastMaxRecDepth 8192 do
  /-
  Note: we need to increase the recursion depth because we currently do to save phase1
  declarations in .olean files. Then, we have to recursively compile all dependencies,
  and it often creates a very deep recursion.
  Moreover, some declarations get very big during simplification.
  -/
  dbg_trace s!">> runWithPasses declnames: {declNames}"
  let declNames ← declNames.filterM (shouldGenerateCode ·)
  if declNames.isEmpty then return #[]
  let mut decls ← declNames.mapM toDecl
  decls := markRecDecls decls
  for pass in passes do
    trace[Compiler] "Running pass: {pass.name}"
    decls ← withPhase pass.phase <| pass.run decls
    withPhase pass.phaseOut <| checkpoint pass.name decls
  if (← Lean.isTracingEnabledFor `Compiler.result) then
    for decl in decls do
      Lean.addTrace `Compiler.result m!"size: {decl.size}\n{← ppDecl decl}"
      -- Lean.addTrace `Compiler.result m!"size: {decl.size}\n{reprStr decl}"
  return decls

end PassManager

def CompilerM.run' (x : CompilerM α) (s : State := {}) (phase : Phase := .base) : 
    CoreM (α × State) := do
  x { phase, config := toConfigOptions (← getOptions) } |>.run s

def compileWithPassesCore (declNames : Array Name) (passes : Array Pass) (recurse? := true) : 
    CoreM (Array Decl × CompilerM.State) := do
  CompilerM.run' <| PassManager.runWithPasses declNames passes recurse?

def compileWithPasses (declNames : Array Name) (passes : Array Pass) (recurse? := true) : 
    CoreM (Array Decl) := do
  let mut queue := declNames
  let mut visited : NameSet := .empty
  let mut res : Array Decl := #[]
  while !queue.isEmpty do
    dbg_trace s!">> compileWithPasses queue: {queue}"
    let (decls, _) ← CompilerM.run' <| PassManager.runWithPasses queue passes recurse?
    dbg_trace s!">> compileWithPasses generated: {decls.map Decl.name}"
    for decl in decls do
      visited := visited.insert decl.name
      res := res.push decl
    let decls := decls.concatMap (·.getUsedConstants)
    let decls := decls.map sanitizeName
    let decls := decls.filter fun decl => !visited.contains decl
    queue := decls
  return res

end LCNF

def compileWithPasses (declNames : Array Name) (passes : Array LCNF.Pass) (recurse? := true) : 
    CoreM Unit := do profileitM Exception "compiler new" (← getOptions) do
  discard <| LCNF.compileWithPassesCore declNames passes recurse?

def toDecl (declName : Name) : CoreM Unit := do
  let decl ← LCNF.CompilerM.run <| LCNF.toDecl declName
  Lean.addTrace `Compiler.result m!"size: {decl.size}\n{← LCNF.ppDecl' decl}"
  return

end Lean.Compiler