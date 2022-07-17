-- import Cli
-- import Yatima.Compiler.Frontend

-- opaque VERSION : String := "0.0.1"

-- open System in
-- partial def getFilePathsList (fp : FilePath) (acc : List FilePath := []) :
--     IO $ List FilePath := do
--   if ← fp.isDir then
--     let mut extra : List FilePath := []
--     for dirEntry in ← fp.readDir do
--       for innerFp in ← getFilePathsList dirEntry.path do
--         extra := extra.concat innerFp
--     return acc ++ extra
--   else
--     if (fp.extension.getD "") = "lean" then
--       return acc.concat fp
--     else
--       return acc

-- def printCompilationStats (stt : Yatima.Compiler.CompileState) : IO Unit := do
--   IO.println $ "\nCompilation stats:\n" ++
--     s!"univ_cache size: {stt.store.univ_cache.size}\n" ++
--     s!"expr_cache size: {stt.store.expr_cache.size}\n" ++
--     s!"const_cache size: {stt.store.const_cache.size}\n" ++
--     s!"cache size: {stt.cache.size}\n" ++
--     s!"cache: {stt.cache.toList.map fun (n, (_, c)) => (n, c.ctorName)}"

-- open Yatima.Compiler in
-- def buildRun (p : Cli.Parsed) : IO UInt32 := do
--   let log : Bool := p.hasFlag "log"
--   match p.variableArgsAs? String with
--   | some ⟨args⟩ =>
--     if !args.isEmpty then
--       let mut stt : CompileState := default
--       let mut errMsg : Option String := none
--       for arg in args do
--         for filePath in ← getFilePathsList ⟨arg⟩ do
--           match ← runFrontend filePath log stt with
--           | .ok stt' => match stt.union stt' with
--             | .ok stt' => stt := stt'
--             | .error msg => errMsg := some msg; break
--           | .error msg => errMsg := some msg; break
--         if errMsg.isSome then break
--       match errMsg with
--       | some msg =>
--         IO.eprintln msg
--         return 1
--       | none => pure ()
--       if log then printCompilationStats stt
--       -- todo: make use of `stt.store`
--       return 0
--     else
--       IO.eprintln "No build argument was found."
--       IO.eprintln "Run `yatima build -h` for further information."
--       return 1
--   | none =>
--     IO.eprintln "Couldn't parse build arguments."
--     IO.eprintln "Run `yatima build -h` for further information."
--     return 1

-- instance : Coe String (Option String) where
--   coe := some

-- def buildCmd : Cli.Cmd := `[Cli|
--   build VIA buildRun; [VERSION]
--   "Compile Lean 4 code to content-addressed IPLD"

--   FLAGS:
--     l, log; "Flag to print compilation progress and stats"

--   ARGS:
--     ...sources : String; "List of Lean files or directories"
-- ]

-- def yatimaCmd : Cli.Cmd := `[Cli|
--   yatima VIA fun _ => pure 0; [VERSION]
--   "A compiler and typechecker for the Yatima language"

--   SUBCOMMANDS:
--     buildCmd
-- ]

-- def main (args : List String) : IO UInt32 :=
--   yatimaCmd.validate args

import Yatima.ToIpld
import Yatima.Store
def main : IO UInt32 := pure 0
