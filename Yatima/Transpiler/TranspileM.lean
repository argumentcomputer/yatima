import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Compiler
import Yatima.Ipld.FromIpld

namespace Yatima.Transpiler

structure State where
  prependedBindings : Array (Name × Lurk.Expr)
  appendedBindings  : Array (Name × Lurk.Expr)
  /-- Contains constants that have already been processed -/
  visited : Std.RBTree Name compare
  deriving Inhabited


def State.getStringBindings (s : State) : List (String × Lurk.Expr) :=
  s.prependedBindings.reverse.append s.appendedBindings |>.data |>.map
    fun (name, lexpr) => (name.toString, lexpr)

open Yatima.Compiler
open Yatima.FromIpld

abbrev TranspileM := ReaderT CompileState $ EStateM String State

def prependBinding (b : Name × Lurk.Expr) : TranspileM Unit := do
  let s ← get
  set $ { s with appendedBindings := s.prependedBindings.push b }

def appendBinding (b : Name × Lurk.Expr) : TranspileM Unit := do
  let s ← get
  set $ { s with appendedBindings := s.appendedBindings.push b }

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit := do 
  set $ { (← get) with visited := (← get).visited.insert name }

def TranspileM.run (store : CompileState) (ste : State) (m : TranspileM α) :
    Except String State :=
  match EStateM.run (ReaderT.run m store) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

end Yatima.Transpiler
