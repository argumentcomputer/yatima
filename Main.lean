import Lean
import Yatima.Cid
import Yatima.Univ
import Yatima.Expr
import Yatima.Const
import Yatima.Env

-- forcing compilation:
import Yatima.Ipld.DagCbor
import Yatima.YatimaSpec

def main : List String → IO UInt32
  | ["build", f] => do
    let input ← IO.FS.readFile f
    Lean.initSearchPath $ ← Lean.findSysroot
    let (env, ok) ← Lean.Elab.runFrontend input .empty f `main
    return 0
  | _ => return 0
