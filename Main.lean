import Lean
import Yatima.DebugUtils
import Yatima.Compiler.Pretty

open Yatima.Compiler.FromLean
open Yatima.Utils

def main : List String → IO UInt32
  | ["build", f] => do
    let input ← IO.FS.readFile ⟨f⟩
    Lean.initSearchPath $ ← Lean.findSysroot
    let (env, ok) ← Lean.Elab.runFrontend input .empty f `main
    --dbg_trace s!"------------"
    --dbg_trace env.constants
    dbg_trace s!"------------"
    -- dbg_trace (filterUnsafeConstants env.constants)
    dbg_trace s!"------------"
    if ok then
      match extractAndPrintEnv (filterUnsafeConstants env.constants) with
      | .ok env => --todo
        return 0
      | .error e =>
        IO.println e
        return 1
    else
      IO.eprintln s!"Lean frontend failed on file {f}"
      return 1
  | _ => return 0
