import Yatima.Store
import Yatima.ForLurkRepo.AST

namespace Yatima.Transpiler

open Yatima (Store)

structure State where
  prependedBindings : Array (String × Lurk.Expr)
  appendedBindings  : Array (String × Lurk.Expr)
  /-- Contains constants that have already been processed -/
  visited : Std.RBTree String compare
  deriving Inhabited

def State.getBindings (s : State) : List (String × Lurk.Expr) :=
  s.prependedBindings.reverse.append s.appendedBindings |>.data

abbrev TranspileM := ReaderT Store $ EStateM String State

def prependBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  let s ← get
  set $ { s with appendedBindings := s.prependedBindings.push b }

def appendBinding (b : String × Lurk.Expr) : TranspileM Unit := do
  let s ← get
  set $ { s with appendedBindings := s.appendedBindings.push b }

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit := do 
  set $ { (← get) with visited := (← get).visited.insert name }

def TranspileM.run (store : Store) (ste : State) (m : TranspileM α) :
    Except String State :=
  match EStateM.run (ReaderT.run m store) ste with
  | .ok _ ste  => .ok ste
  | .error e _ => .error e

end Yatima.Transpiler
