import Lean
import Yatima.Lean.Compile
import Yatima.Lean.RunFrontend

open Lean Elab Command Term Meta

elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

elab "#compile" i:ident : command => do
  logInfo m!"Compiling: {i.getId}"
  liftCoreM <| Lean.Compiler.compile #[i.getId]

open Lean.Compiler LCNF

def Lean.setLibsPaths : IO Unit := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["print-paths"]
  }
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  let paths := split.replace "\"" "" |>.splitOn ","|>.map System.FilePath.mk
  Lean.initSearchPath (← Lean.findSysroot) paths

def Lean.Elab.Frontend.runCore (x : CoreM α) : FrontendM α := do
  let cmd := liftCoreM x
  runCommandElabM cmd

def Lean.Elab.Frontend.compile (decls : Array Name) : FrontendM Unit := do
  let cmd := liftCoreM <| Lean.Compiler.compile decls
  runCommandElabM cmd


partial def Lean.Elab.Frontend.processCore (x : CoreM α) : FrontendM α := do
  processCommands
  runCore x

def IO.processCore 
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState) 
    (commandState : Command.State) (x : CoreM α) : IO (α × Frontend.State) := do
  (Frontend.processCore x |>.run { inputCtx := inputCtx }).run 
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

def Lean.Elab.runCoreFrontend 
    (input : String) (fileName : String := default) (x : CoreM α) : 
    IO (Option α × Environment) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header default messages inputCtx 0
  let env := env.setMainModule default
  let commandState := Command.mkState env messages default

  let (a, s) ← IO.processCore inputCtx parserState commandState x
  for msg in s.commandState.messages.toList do
    IO.print (← msg.toString (includeEndPos := getPrintMessageEndPos default))

  let a := if s.commandState.messages.hasErrors then none else some a
  pure (a, s.commandState.env)

def Lean.Elab.runTestFrontend 
    (input : String) (fileName : String := default) : IO (Bool × Environment) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Yatima.processHeader header default messages inputCtx 0
  let env := env.setMainModule default
  let commandState := Command.mkState env messages default

  let s ← IO.processCommands inputCtx parserState commandState
  IO.println ">> runTestFrontend: print errors"
  for msg in s.commandState.messages.toList do
    IO.print (← msg.toString (includeEndPos := getPrintMessageEndPos default))

  pure (!s.commandState.messages.hasErrors, s.commandState.env)

def passes : Array Pass := #[
  init,
  pullInstances,
  cse,
  simp,
  floatLetIn,
  findJoinPoints,
  pullFunDecls,
  reduceJpArity,
  /-
  We apply `implementedBy` replacements before `specialize` to ensure we specialize the replacement.
  One possible improvement is to perform only the replacements if the target declaration is a specialization target,
  and on phase 2 (aka mono) perform the remaining replacements.
  -/
  simp { etaPoly := true, inlinePartial := true, implementedBy := true } (occurrence := 1),
  eagerLambdaLifting,
  -- specialize,
  simp (occurrence := 2),
  cse (occurrence := 1),
  saveBase, -- End of base phase
  toMono,
  -- simp (occurrence := 3) (phase := .mono),
  reduceJpArity (phase := .mono),
  extendJoinPointContext (phase := .mono) (occurrence := 0),
  floatLetIn (phase := .mono) (occurrence := 1),
  -- reduceArity,
  commonJoinPointArgs,
  -- simp (occurrence := 4) (phase := .mono),
  floatLetIn (phase := .mono) (occurrence := 2),
  lambdaLifting,
  extendJoinPointContext (phase := .mono) (occurrence := 1),
  -- simp (occurrence := 5) (phase := .mono),
  cse (occurrence := 2) (phase := .mono),
  saveMono  -- End of mono phase
]

-- def natSub1 := 100 - 2
def list := [1, 2, 3, 4, 5, 6]
def listMap := list.map fun x => x + 1
-- def listBeq := list == [1, 2, 3, 4, 5, 6]
-- def natMatch : Nat → Nat
--   | 0 => 0
--   | 2 => 5
--   | n + 1 => natMatch n

-- def stringMatch : String → Nat
--   | "a" => 1
--   | _ => 10

-- def name : Lean.Name := `hello
-- #print Name._impl
-- #print Lean.Name.str._override
#print String.hash

set_option trace.Compiler.result true in
#eval Compiler.compileWithPasses #[``Lean.Name.toString] passes

def Lean.Elab.compile (filePath : System.FilePath) (decls : Array Name) (recurse? := true) : 
    IO (Array Decl × Environment) := do
  let input ← IO.FS.readFile filePath
  Lean.setLibsPaths
  let (res, env) ← runCoreFrontend input filePath.toString $ 
    LCNF.compileWithPasses decls passes recurse?
  match res with 
  | some decls => return (decls, env)
  | none => throw $ .userError s!"failed to compile {decls}"

def Lean.Elab.testFrontend (filePath : System.FilePath) (decls : Array Name) : 
    IO Unit := do
  let input ← IO.FS.readFile filePath
  Lean.setLibsPaths
  let (res, env) ← runTestFrontend input filePath.toString
  IO.println ">> testFrontend"
  IO.println s!"res: {res}"
  IO.println s!"`List.map exists? {(Compiler.LCNF.getDeclCore? env Compiler.LCNF.monoExt `List.map).isSome}"
  IO.println $ reprStr $ getDeclCore? env Compiler.LCNF.monoExt `listMap

set_option trace.Compiler.result true
def test : IO UInt32 := do
  let (res, env) ← Lean.Elab.compile "Fixtures/Transpilation/Primitives.lean" #[`Fin.ofNat]
  IO.println s!"res: "
  IO.println $ reprStr res

  return 0

#eval test