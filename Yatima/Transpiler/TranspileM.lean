import Yatima.Store
import Yatima.ForLurkRepo.AST

namespace Yatima.Transpiler

open Yatima (Store)

structure State where 
  /-- 
  Visiting order in our dfs traversal. 
  This is the reverse order of how the bindings should be defined.
  -/
  bindings : Array (String × Lurk.Expr)
  /-- Contains constants that have already been processed -/
  visited : Std.HashSet String 

abbrev TranspileM := ReaderT Store $ EStateM String State

def prependBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  set $ { (← get) with bindings := #[b].append (← get).bindings }

def appendBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  set $ { (← get) with bindings := (← get).bindings.push b }

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit := do 
  set $ { (← get) with visited := (← get).visited.insert name }

def TranspileM.run (store : Store) (ste : State) (m : TranspileM α) :
    Except String State :=
  match EStateM.run (ReaderT.run m store) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

end Yatima.Transpiler
