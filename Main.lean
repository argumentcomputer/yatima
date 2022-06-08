import Lean
import Yatima.FromLean

open Yatima.Compiler.FromLean

def main : List String → IO UInt32
  | ["build", f] => do
    let input ← IO.FS.readFile ⟨f⟩
    Lean.initSearchPath $ ← Lean.findSysroot
    let (env, ok) ← Lean.Elab.runFrontend input .empty f `main
    if ok then
      let l := env.constants.toList.map fun (n, _) => n
      IO.println l
      -- return 0
      match extractEnv env.constants with
      | .ok env => --todo
        return 0
      | .error e =>
        IO.println e
        return 1
    else
      IO.eprintln s!"Lean frontend failed on file {f}"
      return 1
  | _ => return 0
