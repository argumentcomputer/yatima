import Yatima.Compiler.GrinM
import Lean.Expr
open Lean.Compiler.LCNF

def Lean.FVarId.toVar (id : Lean.FVarId) : Yatima.Grin.Var := .mk id.name

namespace Yatima.Grin

def mkFreshVar : GrinM Var := do
  pure ⟨← Lean.mkFreshId⟩

def paramsToVars (params : Array Param) : List Var :=
  params.toList.map (fun param => param.fvarId.toVar)

def fetch? (id : Lean.FVarId) : GrinM SExpr := do
  match ← varKind id with
  | .pointer => pure $ .fetch id.toVar .none
  | .basic => pure $ svar id.toVar

def applyArgs (fnc : Var) : (args : List Arg) → GrinM Expr
| [] => pure $ .ret $ svar fnc
| .erased :: args => applyArgs fnc args
| .type _ :: args => applyArgs fnc args
| .fvar id :: args => do
  let apply := .apply fnc (.var id.toVar)
  let newVar ← mkFreshVar
  let rest ← applyArgs newVar args
  pure $ .seq apply (.svar newVar) rest

mutual
partial def PScheme : Alt → GrinM (CPat × Expr)
| .default code => do
  let expr ← RScheme code
  pure (.default, expr)
| .alt ctor params code  => do
  let args := paramsToVars params
  let tag := .C ⟨ ctor ⟩
  let expr ← RScheme code
  pure (.ctag tag args, expr)

partial def RScheme : Code → GrinM Expr
| .let decl k => match decl.value with
  | .erased => RScheme k
  | .value val => do
    pure $ .ret $ slit val
  | .proj _ idx struct => do
    let structPtr := struct.toVar
    let proj := .fetch structPtr (some idx)
    pure $ .ret proj
  | .const _name _ _args => throw "TODO"
  | .fvar fnc args => do
    let fncVal ← fetch? fnc
    let newVar ← mkFreshVar
    pure $ .seq fncVal (.svar newVar) (← applyArgs newVar args.toList)
| .cases case => do
  let some patExprs := NEList.nonEmpty (← case.alts.toList.mapM PScheme)
    | throw "Empty pattern"
  -- Since every variable is initially strict, we don't need to eval before
  let caseVal ← fetch? case.discr
  let newVar ← mkFreshVar
  let caseExpr := .case (.sval $ .var newVar) patExprs
  pure $ .seq caseVal (.svar newVar) caseExpr
  -- pure expr
| .return fvarId => do
  -- In the lazy case, a return is a call to eval, but since we chose strict semantics this
  -- will either be a `fetch` or `unit` instruction depending on whether the variable is a
  -- pointer or basic value
  pure $ .ret $ ← fetch? fvarId
| .fun _decl _k => throw "Should not find function definition here (?)"
-- We need to figure out a way to implement join points
| .jp _decl _k => throw "TODO"
| .jmp _fvarId _args => throw "TODO"
| .unreach _type => throw "Unreach found"
end

def compileDeclaration (decl : Decl) : GrinM Binding := do
  let defn := ⟨decl.name⟩
  let args := paramsToVars decl.params
  let body ← RScheme decl.value
  let binding := { defn, args, body }
  pure binding

end Yatima.Grin
