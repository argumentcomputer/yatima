import Lean
import Yatima.Typechecker.Infer
import Yatima.Typechecker.FromIPLD
import Yatima.Typechecker.Debug
import Yatima.Compiler.Frontend

def List.pop : (l : List α) → l ≠ [] → α × List α
  | a :: as, _ => (a, as)

open Yatima.Compiler in
def main (args : List String) : IO UInt32 := do
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
