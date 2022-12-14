import Std.Data.List.Basic
import Lurk.Syntax.ExprUtils
import Lurk.Evaluation.FromAST
import Yatima.Datatypes.Lean
import Yatima.Lean.Utils
import Yatima.Transpiler.TranspileM
import Yatima.Transpiler.PrettyPrint
import Yatima.Transpiler.LurkFunctions
import Yatima.Transpiler.Overrides.All

namespace Yatima.Transpiler

open Lurk.Syntax AST DSL
open Lean Compiler.LCNF

def preloads : List (Name × AST) := [
  Lurk.Preloads.reverse_aux,
  Lurk.Preloads.reverse,
  Lurk.Preloads.set,
  Lurk.Preloads.set!,
  Lurk.Preloads.push,
  Lurk.Preloads.append,
  Lurk.Preloads.getelem,
  Lurk.Preloads.getelem!,
  Lurk.Preloads.drop,
  Lurk.Preloads.str_mk,
  Lurk.Preloads.str_data,
  Lurk.Preloads.str_push,
  Lurk.Preloads.str_append,
  Lurk.Preloads.to_bool,
  Lurk.Preloads.lor,
  Lurk.Preloads.land,
  Lurk.Preloads.lnot,
  Lurk.Preloads.lneq
]

def preloadNames : Lean.NameSet :=
  .ofList (preloads.map Prod.fst)

def safeName (name : Name) : TranspileM Name :=
  let nameStr := name.toString false
  if preloadNames.contains name
      || reservedSyms.contains nameStr
      || nameStr.contains '|' then do
    match (← get).replaced.find? name with
    | some n => return n
    | none   => replace name
  else return name

def mkName (name : Name) : TranspileM AST := do
  toAST <$> safeName name

instance : ToAST FVarId where
  toAST fvarId := toAST fvarId.name

instance : ToAST LitValue where toAST
  | .natVal n => toAST n
  | .strVal s => toAST s

def appendBinding (b : Name × AST) (safe := true) : TranspileM Unit := do
  let b := if safe then (← safeName b.1, b.2) else b
  modify fun s => { s with appendedBindings := s.appendedBindings.push b }

def appendInductiveData (data : InductiveData) : TranspileM Unit := do
  modify fun s => { s with inductives := s.inductives.insert data.name data }

def mkIndLiteral (ind : InductiveVal) : TranspileM AST := do
  let (name, params, indices, type) :=
    (ind.name.toString false, ind.numParams, ind.numIndices, ind.type)
  let args ← type.getForallBinderNames.mapM safeName
  -- let args : List AST ← args.mapM fun (n, _) => mkName n
  if args.isEmpty then
    return ⟦,($name $params $indices)⟧
  else
    return ⟦(lambda $args ,($name $params $indices))⟧

/-- TODO explain this; `p` is `params`, `i` is `indices` -/
def splitCtorArgs (args : List AST) (p i : Nat) : List (List AST) :=
  let (params, rest) := args.splitAt p
  let (indices, args) := rest.splitAt i
  [params, indices, args]

def appendConstructor (ctor : ConstructorVal) : TranspileM Unit := do
  let (name, idx, type, induct) := (ctor.name, ctor.cidx, ctor.type, ctor.induct)
  visit ctor.name
  let ctorArgs ← type.getForallBinderNames.mapM mkName
  -- let ctorData := splitCtorArgs ctorArgs ctor.numParams ctor.numIndices
  -- let ctorDataAST := ctorData.map mkConsList
  let ctorData := mkConsList (toAST (induct.toString false) :: toAST idx :: ctorArgs)
  let body := if ctorArgs.isEmpty then
    ctorData
  else
    ⟦(lambda $ctorArgs $ctorData)⟧
  appendBinding (name, body)

/-- Amazingly, we don't actually have to transpile recursors... -/
def appendInductive (ind : InductiveVal) : TranspileM Unit := do
  let (name, params, indices) := (ind.name, ind.numParams, ind.numIndices)
  visit name
  let ctors : List ConstructorVal ← ind.ctors.mapM fun ctor => do
    match (← read).env.constants.find? ctor with
    | some (.ctorInfo ctor) => return ctor
    | _ => throw s!"malformed environment, {ctor} is not a constructor or doesn't exist"
  let ctorData := ctors.foldl (init := .empty)
    fun acc ctor => acc.insert ctor.name ctor.cidx
  appendInductiveData ⟨name, params, indices, ctorData⟩
  appendBinding (name, ← mkIndLiteral ind)
  for ctor in ctors do
    appendConstructor ctor

def getInductive (name : Name) : TranspileM InductiveVal := do
  match (← read).env.constants.find? name with
  | some (.inductInfo ind) => return ind
  | _ => throw s!"{name} is not an inductive"

def getCtorOrIndInfo? (name : Name) : TranspileM $ Option (List Name) := do
  match (← read).env.constants.find? name with
  | some (.inductInfo ind) => return some ind.all
  | some (.ctorInfo ctor) =>
    let ind ← getInductive ctor.induct
    return some ind.all
  | _ => return none

def appendCtorOrInd (name : Name) : TranspileM Bool := do
  match (← read).env.constants.find? name with
  | some (.inductInfo ind) =>
    for ind in ind.all do
      let ind ← getInductive ind
      appendInductive ind
    return true
  | some (.ctorInfo ctor) =>
    let ind ← getInductive ctor.induct
    for ind in ind.all do
      let ind ← getInductive ind
      appendInductive ind
    return true
  | _ => return false

def getMutuals (name : Name) : TranspileM (List Name) := do
  match (← read).env.constants.find? name with
  -- TODO FIXME: support `| some (.inductInfo x)` case
  | some (.defnInfo x) | some (.thmInfo x)| some (.opaqueInfo x) => return x.all
  | _ => return [name]

def mkFVarId : FVarId → TranspileM AST
  | fvarId => do mkName fvarId.name

def mkArg : Arg → TranspileM AST
  | .erased => return toAST "lcErased"
  | .fvar fvarId => mkFVarId fvarId
    -- TODO: Hopefully can erase types??
  | .type _ => return toAST "lcErasedType"

def mkParam : Param → TranspileM AST
  | ⟨fvarId, _, _, _⟩ =>
    mkName fvarId.name

def mkParams (params : Array Param) : TranspileM (Array AST) := do
  params.mapM mkParam

def mkCasesCore (indData : InductiveData) (discr : AST) (alts : Array Override.Alt) :
    Except String AST := do
  let mut defaultElse : AST := .nil
  let mut ifThens : Array (AST × AST) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if params.isEmpty then
        ifThens := ifThens.push (⟦(= _lurk_idx $cidx)⟧, k)
      else
        let params : List (AST × AST) := params.toList.enum.map fun (i, param) =>
          (toAST param, ⟦(getelem _lurk_args $i)⟧)
        let case := ⟦(let $params $k)⟧
        ifThens := ifThens.push (⟦(= _lurk_idx $cidx)⟧, case)
  let cases := mkIfElses ifThens.toList defaultElse
  return ⟦(let ((_lurk_idx (getelem $discr 1))
                (_lurk_args (drop $(2 + indData.params) $discr)))
            $cases)⟧

mutual

  partial def mkLetValue : LetValue → TranspileM AST
    | .value lit => return toAST lit
    | .erased => return toAST "lcErased"
    | .proj _ idx struct =>
      -- TODO FIXME: use `typeName` to get params and add to `idx`
      return ⟦(getelem $idx $struct.name)⟧
    | .const declName _ args => do
      appendName declName
      if args.isEmpty then
        return toAST declName
      else
        return (toAST declName).cons $ toAST (← args.mapM mkArg)
    | .fvar fvarId args =>
      if args.isEmpty then
        mkName fvarId.name
      else
      return (← mkFVarId fvarId).cons $ toAST (← args.mapM mkArg)

  partial def mkLetDecl : LetDecl → TranspileM AST
    | ⟨fvarId, _, _, value⟩ => do
      let fvarId ← safeName fvarId.name
      let value ← mkLetValue value
      return ⟦($fvarId $value)⟧

  partial def mkFunDecl : FunDecl → TranspileM AST
    | ⟨fvarId, _, params, _, value⟩ => do
      let fvarId ← safeName fvarId.name
      let value ← mkCode value
      let params ← params.mapM mkParam
      return ⟦($fvarId (lambda $params $value))⟧

  partial def mkOverrideAlt (indData : InductiveData) :
      Alt → TranspileM Override.Alt
    | .default k => .default <$> mkCode k
    | .alt ctor params k => do
      let some cidx := indData.ctors.find? ctor |
        throw s!"{ctor} not a valid constructor for {indData.name}"
      let params ← params.mapM fun p => safeName p.fvarId.name
      return .alt cidx params (← mkCode k)

  partial def mkOverrideAlts (indData : InductiveData) (alts : Array Alt) :
      TranspileM (Array Override.Alt) := do
    alts.mapM $ mkOverrideAlt indData

  partial def mkCases (cases : Cases) : TranspileM AST := do
    let ⟨typeName, _, discr, alts⟩ := cases
    appendName typeName
    dbg_trace s!">> mkCases typeName: {typeName}"
    let indData := ← match (← get).inductives.find? typeName with
      | some data => return data
      | none => throw s!"{typeName} is not an inductive"
    let discr ← mkFVarId discr
    let alts ← mkOverrideAlts indData alts
    match (← read).overrides.find? typeName with
    | some (.ind ind) => liftExcept <| ind.mkCases discr alts
    | none            => liftExcept <| mkCasesCore indData discr alts
    | some (.decl _)  => throw s!"found a declaration override for {typeName}"

  partial def mkCode : Code → TranspileM AST
    | .let decl k => do
      let decl ← mkLetDecl decl
      let k ← mkCode k
      return ⟦(let ($decl) $k)⟧
    | .fun decl k | .jp decl k => do -- `.fun` and `.jp` are the same case to Lurk
      let decl ← mkFunDecl decl
      let k ← mkCode k
      return ⟦(let ($decl) $k)⟧
    | .jmp fvarId args => do
      let fvarId ← mkFVarId fvarId
      let args ← args.mapM mkArg
      return .cons fvarId (toAST args)
    | .cases cases => mkCases cases
    | .return fvarId => mkFVarId fvarId
    | .unreach _ => return toAST "lcUnreachable"

  partial def appendDecl (decl : Decl) : TranspileM Unit := do
    dbg_trace s!">> appendDecl\n{ppDecl decl}\n"
    let ⟨name, _, _, params, value, _, _, _⟩ := decl
    visit name
    let params : Array AST := params.map fun p => toAST p.fvarId.name
    let value : AST ← mkCode value
    let body := if params.isEmpty
      then value
      else ~[.sym "LAMBDA", toAST params, value]
    appendBinding (name, body)
  
  partial def appendMutualDecls (decls : List Decl) : TranspileM Unit := do
    dbg_trace s!">> appendMutualDecls"
    for decl in decls do
      visit decl.name
    let decls ← decls.mapM fun decl => do
      dbg_trace ppDecl decl
      let ⟨name, _, _, params, value, _, _, _⟩ := decl
      let params : Array AST := params.map fun p => toAST p.fvarId.name
      let value : AST ← mkCode value
      let body := if params.isEmpty
        then value
        else ~[.sym "LAMBDA", toAST params, value]
      return (name.toString, body) -- TODO FIXME: this is pretty dangerous `toString`
    match AST.mkMutualBlock decls with
    | .ok xs => xs.forM fun (n, e) => appendBinding (n, e)
    | .error e => throw e

  partial def appendName (name : Name) : TranspileM Unit := do
    if (← get).visited.contains name then
      return
    dbg_trace s!">> appendName new name {name}"
    match ← getCtorOrIndInfo? name with
    | some inds =>
      for ind in inds do
        if ← appendOverride ind then
          continue
        let ind ← getInductive ind
        appendInductive ind
    | none =>
      let names ← getMutuals name
      if let [name] := names then 
        if ← appendOverride name then return
        appendDecl $ ← getMonoDecl name
      else
        -- TODO FIXME: no support for mutual overrides
        appendMutualDecls $ ← names.mapM getMonoDecl

  partial def appendOverride (name : Name) : TranspileM Bool := do
    dbg_trace s!">> appendOverride {name}"
    match (← read).overrides.find? name with
    | some (.decl ⟨name, decl⟩) =>
      visit name
      appendPrereqs decl
      appendBinding (name, decl)
      return true
    | some (.ind ⟨indData, ⟨name, decl⟩, ctors, _⟩) =>
      visit name
      appendInductiveData indData
      appendPrereqs decl
      appendBinding (name, decl)
      for ⟨name, ctor⟩ in ctors do
        visit name
        appendPrereqs ctor
        appendBinding (name, ctor)
      return true
    | none => return false
  where
    appendPrereqs (x : AST) : TranspileM Unit := do
      match x.getFreeVars with
      | .error err => throw err
      | .ok fVars => 
        dbg_trace s!">> appendPrereqs fvars: {fVars.toList}"
        fVars.toList.forM fun n => do
          let n := n.toNameSafe
          if !(← isVisited n) then appendName n

end

/-- Main translation function -/
def transpileM (root : Lean.Name) : TranspileM Unit :=
  let overrides := .ofList <| Lurk.Overrides.All.module.map fun o => (o.name, o)
  withOverrides overrides do
    dbg_trace s!">> transpileM overrides: {(← read).overrides.toList.map Prod.fst}"
    preloads.forM fun (name, preload) => do
      visit name
      appendBinding (name, preload) false
    appendName root

/--
Constructs a `AST.letRecE` whose body is the call to a `root` constant in
a context and whose bindings are the constants in the context (including `root`)
that are needed to define `root`.
-/
def transpile (filePath : System.FilePath) (root : Name) : 
    IO $ Except String Lurk.Evaluation.Expr := do
  let filePathStr := filePath.toString
  Lean.setLibsPaths
  match ← Lean.runFrontend (← IO.FS.readFile filePath) filePathStr with
  | (some err, _) => return .error err
  | (none, env) =>
    let transpileEnv := ⟨env, .empty⟩
    match TranspileM.run transpileEnv default (transpileM root) with
    | .ok _ s =>
      let bindings := s.appendedBindings.data.map
        fun (n, x) =>
          dbg_trace s!">> transpile {n}: {x}"
          (n.toString false, x)
      let ast := mkLetrec bindings (.sym $ root.toString false)
      let ast := ast.pruneBlocks
      let ast := ast >>= AST.toExpr
      return ast
    | .error e _ => .error e


end Yatima.Transpiler
