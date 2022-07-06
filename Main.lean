import Lean
import Yatima.Compiler.Frontend
import Cli

open Cli

constant VERSION : String := "0.0.1"

open Yatima.Compiler in
def buildRun (p : Parsed) : IO UInt32 := do
  let log : Bool := p.hasFlag "log"
  match p.variableArgsAs? String with
  | some ⟨args⟩ =>
    if h : args ≠ [] then
      let mut stt : CompileState := default
      for arg in args do
        -- check if arg is a folder or a lean file
        -- if it's a lean file, compile it
        -- if it's a folder, compile every lean file inside it
        -- always pass the resulting state to the next compilation call
        return 1 -- in case of error
      return 0 -- compilation went fine
    else
      IO.eprintln "No build argument was found."
      IO.eprintln "Run `yatima build -h` for further information."
      return 1
  | none =>
    IO.eprintln "Couldn't parse build arguments."
    IO.eprintln "Run `yatima build -h` for further information."
    return 1

def buildCmd : Cmd := `[Cli|
  build VIA buildRun; [VERSION]
  "todo"

  FLAGS:
    l, log; "todo"

  ARGS:
    ...sources : String; "todo"
]

def yatimaCmd : Cmd := `[Cli|
  yatima VIA fun _ => pure 0; [VERSION]
  "A compiler and typechecker for the Yatima language"

  SUBCOMMANDS:
    buildCmd
]

def main (args : List String) : IO UInt32 :=
  yatimaCmd.validate args

#exit

def List.pop : (l : List α) → l ≠ [] → α × List α
  | a :: as, _ => (a, as)

open Yatima.Compiler in
def main' (args : List String) : IO UInt32 := do
  if h : args ≠ [] then
    let (cmd, args) := args.pop h
    match cmd with
    | "build" =>
      if h : args ≠ [] then
        let (fileName, args) := args.pop h
        match ← runFrontend (← IO.FS.readFile ⟨fileName⟩) fileName
          (args.contains "-pl") (args.contains "-py") with
        | .error err => IO.eprintln err; return 1
        | .ok env =>
          -- todo: write to .ya
          return 0
      else
        -- todo: print help
        return 0
    | _ =>
      -- todo: print help
      return 0
  else
    -- todo: print help
    return 0
