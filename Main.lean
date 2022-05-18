import Lean
import Yatima.Cid
import Yatima.Univ
import Yatima.Expr
import Yatima.Const
import Yatima.Env
import Yatima.FromLean

-- forcing compilation:
import Yatima.Ipld.DagCbor
import Yatima.YatimaSpec

import Std

open Yatima

def main : List String → IO UInt32
  | ["build", f] => do
    let input ← IO.FS.readFile ⟨f⟩
    Lean.initSearchPath $ ← Lean.findSysroot
    let (env, ok) ← Lean.Elab.runFrontend input .empty f `main
    if ok then
      let mut yatimaConsts : Std.HashMap Name Const := default
      for (nam, c) in env.constants.toList do
        match Lean.Yatima.Compiler.toYatimaConst env.constants c with
          | .ok    c => yatimaConsts := yatimaConsts.insert nam c
          | .error s => IO.eprintln s; return 1
      let env : Env := {
        univs := sorry
        exprs := sorry
        consts := sorry

        univ_anon := sorry
        expr_anon := sorry
        const_anon := sorry

        univ_meta := sorry
        expr_meta := sorry
        const_meta := sorry
      }
      return 0
    else
      IO.eprintln s!"Lean frontend failed on file {f}"
      return 1
  | _ => return 0
