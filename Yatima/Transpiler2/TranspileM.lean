import Lurk.Syntax.AST
import Lean.CoreM
import Lean.Compiler.LCNF.LCtx
import Yatima.Transpiler2.Override

namespace Yatima.Transpiler2

open Lurk.Syntax (AST)

open Lean.Compiler.LCNF Lean.Core

structure TranspileEnv where
  lctx : LCtx
  decls : Lean.NameMap Decl
  constants : Lean.ConstMap
  overrides : Lean.NameMap Override

structure TranspileState where
  appendedBindings : Array (Lean.Name × AST)
  /-- Contains the names of constants that have already been processed -/
  visited  : Lean.NameSet
  inductives : Lean.NameMap InductiveData
  deriving Inhabited
  
abbrev TranspileM := ReaderT TranspileEnv $ EStateM String TranspileState

/-- Set `name` as a visited node -/
def visit (name : Lean.Name) : TranspileM Unit :=
  modify fun s => { s with visited := s.visited.insert name }

@[inline] def isVisited (n : Lean.Name) : TranspileM Bool :=
  return (← get).visited.contains n

def getBinderName (fvarId : Lean.FVarId) : TranspileM Lean.Name := do
  let lctx := (← read).lctx
  if let some decl := lctx.letDecls.find? fvarId then
    return decl.binderName
  else if let some decl := lctx.params.find? fvarId then
    return decl.binderName
  else if let some decl := lctx.funDecls.find? fvarId then
    return decl.binderName
  else
    throw "unknown free variable {fvarId.name}"

def withOverrides (overrides : Lean.NameMap Override) : TranspileM α → TranspileM α :=
  fun x => withReader (fun env => { env with overrides := overrides }) x

def TranspileM.run (env : TranspileEnv) (s : TranspileState) (m : TranspileM α) : 
    EStateM.Result String TranspileState α :=
  m env |>.run s

end Yatima.Transpiler2
