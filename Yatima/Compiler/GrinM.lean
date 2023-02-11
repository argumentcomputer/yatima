import Yatima.Compiler.Grin

open Lean.Compiler.LCNF

namespace Yatima.Grin

-- The Grin compiler monad
structure GrinEnv where
  varKind : Lean.NameMap VarKind
  env : Lean.Environment

structure GrinState where
  bindings : Lean.NameMap Binding
  visited  : Lean.NameSet
  ngen     : Lean.NameGenerator
  deriving Inhabited

abbrev GrinM := ReaderT GrinEnv $ EStateM String GrinState

instance : Lean.MonadNameGenerator GrinM where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen := ngen }

def visit (name : Lean.Name) : GrinM Unit :=
  modify fun s => { s with visited := s.visited.insert name }

@[inline] def isVisited (n : Lean.Name) : GrinM Bool :=
  return (← get).visited.contains n

@[inline] def varKind (n : Lean.FVarId) : GrinM VarKind := do
  match (← read).varKind.find? n.name with
  | some kind => pure kind
  | none => throw "Unknown variable"

@[inline] def getBinding (n : Lean.FVarId) : GrinM Binding := do
  match (← get).bindings.find? n.name with
  | some binding => pure binding
  | none => throw "Unknown variable"

@[inline] def addBinding (n : Lean.FVarId) (binding : Binding) : GrinM Unit :=
  modify (fun state => { state with bindings := state.bindings.insert n.name binding })

def GrinM.run (env : GrinEnv) (s : GrinState) (m : GrinM α) :
    EStateM.Result String GrinState α :=
  m env |>.run s

def getDecl (declName : Lean.Name) : GrinM Decl := do
  let env := (← read).env
  let some decl := getDeclCore? env monoExt declName
    | throw s!"environment does not contain {declName}"
  pure decl

end Yatima.Grin
