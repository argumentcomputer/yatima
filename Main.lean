import Cli
import Yatima.Compiler.Frontend
import Yatima.Typechecker.Infer
import Yatima.Typechecker.FromIPLD
import Yatima.Typechecker.Debug

opaque VERSION : String := "0.0.1"

open System in
partial def getFilePathsList (fp : FilePath) (acc : List FilePath := []) :
    IO $ List FilePath := do
  if ← fp.isDir then
    let mut extra : List FilePath := []
    for dirEntry in ← fp.readDir do
      for innerFp in ← getFilePathsList dirEntry.path do
        extra := extra.concat innerFp
    return acc ++ extra
  else
    if (fp.extension.getD "") = "lean" then
      return acc.concat fp
    else
      return acc

def printCompilationStats (stt : Yatima.Compiler.CompileState) : IO Unit := do
  IO.println $ "\nCompilation stats:\n" ++
    s!"univ_cache size: {stt.store.univ_cache.size}\n" ++
    s!"expr_cache size: {stt.store.expr_cache.size}\n" ++
    s!"const_cache size: {stt.store.const_cache.size}\n" ++
    s!"cache size: {stt.cache.size}\n" ++
    s!"cache: {stt.cache.toList.map fun (n, (_, c)) => (n, c.ctorName)}"

open Yatima.Typechecker in
open Yatima.Compiler in
def storeRun (p : Cli.Parsed) : IO UInt32 := do
  let log : Bool := p.hasFlag "log"
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if !args.isEmpty then
      let mut stt : CompileState := default
      let mut errMsg : Option String := none
      for arg in args do
        for filePath in ← getFilePathsList ⟨arg⟩ do
          match ← runFrontend filePath log stt with
          | .ok stt' => match stt.union stt' with
            | .ok stt' => stt := stt'
            | .error msg => errMsg := some msg; break
          | .error msg => errMsg := some msg; break
        if errMsg.isSome then break
      match errMsg with
      | some msg =>
        IO.eprintln msg
        return 1
      | none => pure ()
      if log then printCompilationStats stt
      let exprs ← convertStoreIO stt.store
      List.forM exprs (fun expr => IO.println s!"{printExpr expr}")
      return 0
    else
      IO.eprintln "No store argument was found."
      IO.eprintln "Run `yatima store -h` for further information."
      return 1
  | none =>
    IO.eprintln "Couldn't parse store arguments."
    IO.eprintln "Run `yatima store -h` for further information."
    return 1

instance : Coe String (Option String) where
  coe := some

def storeCmd : Cli.Cmd := `[Cli|
  store VIA storeRun; [VERSION]
  "Compile Lean 4 code to content-addressed IPLD"

  FLAGS:
    l, log; "Flag to print compilation progress and stats"

  ARGS:
    ...sources : String; "List of Lean files or directories"
]

def yatimaCmd : Cli.Cmd := `[Cli|
  yatima NOOP; [VERSION]
  "A compiler and typechecker for the Yatima language"

  SUBCOMMANDS:
    storeCmd
]

def main (args : List String) : IO UInt32 :=
  yatimaCmd.validate args
