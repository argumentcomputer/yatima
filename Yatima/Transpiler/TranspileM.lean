import Yatima.Ipld.FromIpld
import Yatima.Transpiler.TranspileError

namespace Yatima.Transpiler

structure State where
  appendedBindings  : Array (Name × Lurk.Expr)
  /-- Contains constants that have already been processed -/
  visited : Std.RBTree Name compare
  deriving Inhabited

open Yatima.Compiler Yatima.FromIpld

abbrev TranspileM := ReaderT CompileState $
  ExceptT TranspileError $ StateT State IO

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit := do 
  IO.println s!"visit {name}"
  set $ { (← get) with visited := (← get).visited.insert name }
  IO.println (← get).visited.toList

def appendBindingNoVisit (b : Name × Lurk.Expr) : TranspileM Unit := do
  IO.println "\n========================================="
  IO.println    b.1
  IO.println   "========================================="
  IO.println s!"{b.2.pprint false |>.pretty 50}"
  IO.println   "========================================="
  let s ← get
  set $ { s with appendedBindings := s.appendedBindings.push b }

def appendBinding (b : Name × Lurk.Expr) : TranspileM Unit := do
  visit b.1
  IO.println "\n========================================="
  IO.println    b.1
  IO.println   "========================================="
  IO.println s!"{b.2.pprint false |>.pretty 50}"
  IO.println   "========================================="
  let s ← get
  set $ { s with appendedBindings := s.appendedBindings.push b }

def TranspileM.run (store : CompileState) (ste : State) (m : TranspileM α) :
    IO $ Except String State := do
  match ← StateT.run (ReaderT.run m store) ste with
  | (.ok _, ste)  => return .ok ste
  | (.error e, _) => return .error (toString e)

end Yatima.Transpiler
