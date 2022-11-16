import Yatima.Transpiler.TranspileError
import Yatima.Datatypes.Store
import Lurk.Syntax.AST

namespace Yatima.Transpiler

open Lurk.Syntax (AST)

structure TranspileEnv where
  irStore  : IR.Store
  tcStore  : TC.Store
  /-- Used to speed up lookup by name -/
  map      : Std.RBMap Name TC.Const compare
  builtins : List (Name × AST)

structure TranspileState where
  appendedBindings : Array (Name × AST)
  /-- Contains constants that have already been processed -/
  visited  : Lean.NameSet
  ngen     : Lean.NameGenerator
  replaced : Lean.NameMap Name
  deriving Inhabited

abbrev TranspileM := ReaderT TranspileEnv $
  ExceptT TranspileError $ StateM TranspileState

instance : Lean.MonadNameGenerator TranspileM where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen := ngen }

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit := do
  -- dbg_trace s!">> visit {name}"
  modify fun s => { s with visited := s.visited.insert name }

/-- Create a fresh variable `_x_n` to replace `name` and update `replaced` -/
def replaceFreshId (name : Name) : TranspileM Name := do
  let name' ← Lean.mkFreshId
  -- dbg_trace s!">> mk fresh name {name'}"
  set $ { (← get) with replaced := (← get).replaced.insert name name'}
  return name'

def appendBuiltinBinding (b : Name × AST) (vst := true) : TranspileM Unit := do
  let s ← get
  set $ { s with appendedBindings := s.appendedBindings.push b }
  if vst then visit b.1

def appendYatimaBinding (b : Name × AST) (vst := true) : TranspileM Unit := do
  let s ← get
  -- let name := "|" ++ b.1.toString false ++ "|"
  set $ { s with appendedBindings := s.appendedBindings.push b }
  if vst then visit b.1

def TranspileM.run (env : TranspileEnv) (ste : TranspileState)
    (m : TranspileM α) : Except String TranspileState := do
  match StateT.run (ReaderT.run m env) ste with
  | (.ok _, ste)  => .ok ste
  | (.error e, _) => .error (toString e)

end Yatima.Transpiler
