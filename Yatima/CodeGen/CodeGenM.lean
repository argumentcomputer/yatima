import Yatima.CodeGen.Override

namespace Yatima.CodeGen

open Lurk.Backend
open Lean.Compiler.LCNF Lean.Core

structure CodeGenEnv where
  env : Lean.Environment
  overrides : Lean.NameMap Override

structure CodeGenState where
  appendedBindings : Array (Lean.Name × Expr)
  /-- Contains the names of constants that have already been processed -/
  visited  : Lean.NameSet
  inductives : Lean.NameMap InductiveData
  ngen     : Lean.NameGenerator
  replaced : Lean.NameMap Lean.Name
  deriving Inhabited

abbrev CodeGenM := ReaderT CodeGenEnv $ EStateM String CodeGenState

instance : Lean.MonadNameGenerator CodeGenM where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen := ngen }

/-- Create a fresh variable to replace `name` and update `replaced` -/
def replace (name : Lean.Name) : CodeGenM Lean.Name := do
  let mut name' ← Lean.mkFreshId
  let env ← read
  while env.env.contains name' || env.overrides.contains name' do
    -- making sure we don't hit an existing name
    name' ← Lean.mkFreshId
  modifyGet fun stt => (name', { stt with
    replaced := stt.replaced.insert name name' })

/-- Set `name` as a visited node -/
def visit (name : Lean.Name) : CodeGenM Unit :=
  modify fun s => { s with visited := s.visited.insert name }

@[inline] def isVisited (n : Lean.Name) : CodeGenM Bool :=
  return (← get).visited.contains n

def getDecl (declName : Lean.Name) : CodeGenM Decl := do
  if let some decl := getDeclCore? (← read).env monoExt declName then
    return decl
  else if let some decl := getDeclCore? (← read).env baseExt declName then
    return decl
  else
    throw s!"environment does not contain {declName}"

def withOverrides (overrides : Lean.NameMap Override) : CodeGenM α → CodeGenM α :=
  withReader fun env => { env with overrides := overrides }

def CodeGenM.run (env : CodeGenEnv) (s : CodeGenState) (m : CodeGenM α) :
    EStateM.Result String CodeGenState α :=
  m env |>.run s

end Yatima.CodeGen
