import Yatima.Transpiler.TranspileError
import Yatima.Datatypes.Store
import Lurk.Syntax.AST

namespace Yatima.Transpiler

open Lurk.Syntax (AST)

structure TranspileEnv where
  irStore : IR.Store
  tcStore : TC.Store
  /-- Used to speed up lookup by name -/
  map : Std.RBMap Name TC.Const compare
  overrides : Std.RBMap Name AST compare

structure TranspileState where
  appendedBindings : Array (Name × AST)
  /-- Contains the names of constants that have already been processed -/
  visited  : Lean.NameSet
  /-- These will help us replace hygienic/clashing names -/
  ngen         : Lean.NameGenerator
  replacedMap  : Lean.NameMap Name
  replacements : Lean.NameSet
  deriving Inhabited

abbrev TranspileM := ReaderT TranspileEnv $
  ExceptT TranspileError $ StateM TranspileState

instance : Lean.MonadNameGenerator TranspileM where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen := ngen }

/-- Set `name` as a visited node -/
def visit (name : Name) : TranspileM Unit :=
  modify fun s => { s with visited := s.visited.insert name }

/-- Create a fresh variable `x.n` to replace `name` and update `replaced` -/
def replace (name : Name) : TranspileM Name := do
  let mut name' ← Lean.mkFreshId
  let replacements := (← get).replacements
  while replacements.contains name' do
    name' ← Lean.mkFreshId
  modifyGet fun stt => (name', { stt with
    replacedMap  := stt.replacedMap.insert name name'
    replacements := stt.replacements.insert name' })

@[inline] def isVisited (n : Name) : TranspileM Bool :=
  return (← get).visited.contains n

def derefConst (i : TC.ConstIdx) : TranspileM TC.Const := do
  let consts := (← read).tcStore.consts
  let size := consts.size
  if h : i < size then
    return consts[i]
  else throw $ .custom s!"invalid index {i} for array of constats with size {size}"

def TranspileM.run (env : TranspileEnv) (ste : TranspileState)
    (m : TranspileM α) : Except String TranspileState := do
  match StateT.run (ReaderT.run m env) ste with
  | (.ok _, ste)  => .ok ste
  | (.error e, _) => .error (toString e)

end Yatima.Transpiler
