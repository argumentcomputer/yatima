import Yatima.Transpiler.TranspileError

namespace Yatima.Transpiler

open Yatima.Compiler

structure TranspileState where
  appendedBindings  : Array (Name × Lurk.Expr)
  /-- Contains constants that have already been processed -/
  visited : Std.RBTree Name compare
  deriving Inhabited

abbrev TranspileM := ReaderT CompileState $
  ExceptT TranspileError $ StateT TranspileState Id

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit := do
  set $ { (← get) with visited := (← get).visited.insert name }

def appendBinding (b : Name × Lurk.Expr) (vst := true) : TranspileM Unit := do
  let s ← get
  set $ { s with appendedBindings := s.appendedBindings.push b }
  if vst then visit b.1

def TranspileM.run (compileState : CompileState) (ste : TranspileState)
    (m : TranspileM α) : Except String TranspileState := do
  match StateT.run (ReaderT.run m compileState) ste with
  | (.ok _, ste)  => .ok ste
  | (.error e, _) => .error (toString e)

end Yatima.Transpiler
