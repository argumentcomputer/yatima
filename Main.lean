import Lean
import Yatima.Compiler.FromLean

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
        let input ← IO.FS.readFile ⟨fileName⟩
        Lean.initSearchPath $ ← Lean.findSysroot
        let (env, ok) ← Lean.Elab.runFrontend input .empty fileName `main
        if ok then
          match extractEnv env.constants
            (args.contains "-pl") (args.contains "-py") with
          | .ok env =>
            -- todo: compile to .ya
            return 0
          | .error e =>
            IO.println e
            return 1
        else
          IO.eprintln s!"Lean frontend failed on file {fileName}"
          return 1
      else
        -- todo: print help
        return 0
    | _ =>
      -- todo: print help
      return 0
  else
    -- todo: print help
    return 0
