import Std.Data.List.Basic
import Yatima.Datatypes.Lean
import Yatima.Lean.Utils
import Yatima.Transpiler.TranspileM
import Yatima.Transpiler.PrettyPrint
import Yatima.Transpiler.LurkFunctions
import Yatima.Transpiler.Overrides.All

namespace Yatima.Transpiler

open Lurk.Backend Expr DSL
open Lean.Compiler.LCNF

def preloads : List (Name × Expr) := [
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
  -- dbg_trace s!">> safeName {name}"
  let nameStr := name.toString false
  if preloadNames.contains name
      -- || reservedSyms.contains nameStr
      || nameStr.contains '|' then do
    match (← get).replaced.find? name with
    | some n => return n
    | none   => replace name
  else
    -- dbg_trace s!">> safeName end {name}"
    return name

def mkName (name : Name) : TranspileM Expr := do
  -- dbg_trace s!">> mkName {name}"
  toExpr <$> safeName name

instance : ToExpr Lean.FVarId where
  toExpr fvarId := toExpr fvarId.name

instance : ToExpr LitValue where toExpr
  | .natVal n => toExpr n
  | .strVal s => toExpr s

def appendBinding (b : Name × Expr) (safe := true) : TranspileM Unit := do
  -- dbg_trace s!">> appendBinding {b.1}"
  let b := if safe then (← safeName b.1, b.2) else b
  modify fun s => { s with appendedBindings := s.appendedBindings.push b }

def appendInductiveData (data : InductiveData) : TranspileM Unit := do
  modify fun s => { s with inductives := s.inductives.insert data.name data }

def mkIndLiteral (ind : Lean.InductiveVal) : TranspileM Expr := do
  -- dbg_trace s!">> mkIndLiteral"
  let (name, params, indices, type) :=
    (ind.name.toString false, ind.numParams, ind.numIndices, ind.type)
  let args ← type.getForallBinderNames.mapM safeName
  let args := args.map (·.toString false)
  if args.isEmpty then
    return ⟦,($name $params $indices)⟧
  else
    return .mkLambda args ⟦,($name $params $indices)⟧

/-- TODO explain this; `p` is `params`, `i` is `indices` -/
def splitCtorArgs (args : List Expr) (p i : Nat) : List (List Expr) :=
  let (params, rest) := args.splitAt p
  let (indices, args) := rest.splitAt i
  [params, indices, args]

def appendConstructor (ctor : Lean.ConstructorVal) : TranspileM Unit := do
  -- dbg_trace s!">> appendConstructor"
  let (name, idx, type, ind) := (ctor.name, ctor.cidx, ctor.type, ctor.induct)
  visit ctor.name
  let ctorArgs ← type.getForallBinderNames.mapM safeName
  let ind := ind.toString false
  let ctorData := ⟦(cons $ind (cons $idx $(mkConsListWith $ ctorArgs.map toExpr)))⟧
  let body := if ctorArgs.isEmpty then
    ctorData
  else
    .mkLambda (ctorArgs.map (·.toString false)) ctorData
  appendBinding (name, body)

/-- Amazingly, we don't actually have to transpile recursors... -/
def appendInductive (ind : Lean.InductiveVal) : TranspileM Unit := do
  -- dbg_trace s!">> appendInductive"
  let (name, params, indices) := (ind.name, ind.numParams, ind.numIndices)
  visit name
  let ctors : List Lean.ConstructorVal ← ind.ctors.mapM fun ctor => do
    match (← read).env.constants.find? ctor with
    | some (.ctorInfo ctor) => return ctor
    | _ => throw s!"malformed environment, {ctor} is not a constructor or doesn't exist"
  let ctorData := ctors.foldl (init := .empty)
    fun acc ctor => acc.insert ctor.name ctor.cidx
  appendInductiveData ⟨name, params, indices, ctorData⟩
  appendBinding (name, ← mkIndLiteral ind)
  for ctor in ctors do
    appendConstructor ctor

def getInductive (name : Name) : TranspileM Lean.InductiveVal := do
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

def mkFVarId : Lean.FVarId → TranspileM Expr
  | fvarId => do
    -- dbg_trace s!">> mkFVarId"
    mkName fvarId.name

def mkArg (arg : Arg) : TranspileM Expr := do
  -- dbg_trace s!">> mkArg"
  match arg with
  | .erased => return toExpr "lcErased"
  | .fvar fvarId => mkFVarId fvarId
    -- TODO: Hopefully can erase types??
  | .type _ => return toExpr "lcErasedType"

def mkParam : Param → TranspileM String
  | ⟨fvarId, _, _, _⟩ =>
    -- dbg_trace s!">> mkParam"
    return (← safeName fvarId.name).toString false

def mkParams (params : Array Param) : TranspileM (Array String) := do
  params.mapM mkParam

def mkCasesCore (indData : InductiveData) (discr : Expr) (alts : Array Override.Alt) :
    Except String Expr := do
  -- dbg_trace s!">> mkCases mkCasesCore: {indData.name}"
  let mut defaultElse : Expr := .atom .nil
  let mut ifThens : Array (Expr × Expr) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      if params.isEmpty then
        ifThens := ifThens.push (⟦(= _lurk_idx $cidx)⟧, k)
      else
        let params : List (String × Expr) := params.toList.enum.map fun (i, param) =>
          (param.toString false, ⟦(getelem _lurk_args $i)⟧)
        let case := mkLet params k
        ifThens := ifThens.push (⟦(= _lurk_idx $cidx)⟧, case)
  let cases := mkIfElses ifThens.toList defaultElse
  return ⟦(let ((_lurk_idx (getelem $discr 1))
                (_lurk_args (drop $(2 + indData.params) $discr)))
            $cases)⟧

mutual

  partial def mkLetValue (letv : LetValue) : TranspileM Expr := do
    -- dbg_trace s!">> mkLetValue"
    match letv with
    | .value lit => return toExpr lit
    | .erased => return toExpr "lcErased"
    | .proj typeName idx struct => do
      appendName typeName
      -- TODO FIXME: use `typeName` to get params and add to `idx`
      -- TODO FIXME: support overrides; this is somewhat non-trivial
      let some indData := (← get).inductives.find? typeName |
        throw s!"{typeName} is not an inductive"
      return ⟦(getelem $struct.name $(2 + indData.params + idx))⟧
    | .const declName _ args => do
      appendName declName
      if args.isEmpty then
        return toExpr declName
      else
        return mkApp (toExpr declName) $ (← args.mapM mkArg).data
    | .fvar fvarId args =>
      if args.isEmpty then
        mkName fvarId.name
      else
        return mkApp (← mkFVarId fvarId) $ (← args.mapM mkArg).data

  partial def mkLetDecl : LetDecl → TranspileM (String × Expr)
    | ⟨fvarId, _, _, value⟩ => do
      -- dbg_trace s!">> mkLetDecl"
      let fvarId ← safeName fvarId.name
      let fvarId := fvarId.toString false
      let value ← mkLetValue value
      return (fvarId, value)

  partial def mkFunDecl : FunDecl → TranspileM (String × Expr)
    | ⟨fvarId, _, params, _, value⟩ => do
      -- dbg_trace s!">> mkFunDecl"
      let fvarId ← safeName fvarId.name
      let fvarId := fvarId.toString false
      let value ← mkCode value
      let ⟨params⟩ ← mkParams params
      return (fvarId, mkLambda params value)

  partial def mkOverrideAlt (indData : InductiveData) :
      Alt → TranspileM Override.Alt
    | .default k => .default <$> mkCode k
    | .alt ctor params k => do
      -- dbg_trace s!">> mkOverrideAlt"
      let some cidx := indData.ctors.find? ctor |
        throw s!"{ctor} not a valid constructor for {indData.name}"
      let params ← params.mapM fun p => safeName p.fvarId.name
      return .alt cidx params (← mkCode k)

  partial def mkOverrideAlts (indData : InductiveData) (alts : Array Alt) :
      TranspileM (Array Override.Alt) := do
    alts.mapM $ mkOverrideAlt indData

  partial def mkCases (cases : Cases) : TranspileM Expr := do
    let ⟨typeName, _, discr, alts⟩ := cases
    appendName typeName
    -- dbg_trace s!">> mkCases typeName: {typeName}"
    let indData := ← match (← get).inductives.find? typeName with
      | some data => return data
      | none => throw s!"{typeName} is not an inductive"
    let discr ← mkFVarId discr
    let alts ← mkOverrideAlts indData alts
    match (← read).overrides.find? typeName with
    | some (.ind ind) => liftExcept <| ind.mkCases discr alts
    | none            => liftExcept <| mkCasesCore indData discr alts
    | some (.decl _)  => throw s!"found a declaration override for {typeName}"

  partial def mkCode (code : Code) : TranspileM Expr := do
    match code with
    | .let decl k => do
      -- dbg_trace s!">> mkCode let"
      let (name, decl) ← mkLetDecl decl
      let k ← mkCode k
      return .let name decl k
    | .fun decl k | .jp decl k => do -- `.fun` and `.jp` are the same case to Lurk
      -- dbg_trace s!">> mkCode fun"
      let (name, decl) ← mkFunDecl decl
      let k ← mkCode k
      return .let name decl k
    | .jmp fvarId args => do
      -- dbg_trace s!">> mkCode jmp"
      let fvarId ← mkFVarId fvarId
      let args ← args.mapM mkArg
      return mkApp fvarId args.data
    | .cases cases =>
      -- dbg_trace s!">> mkCode cases"
      mkCases cases
    | .return fvarId =>
      -- dbg_trace s!">> mkCode return {fvarId.name}"
      mkFVarId fvarId
    | .unreach _ => return toExpr "lcUnreachable"

  partial def appendDecl (decl : Decl) : TranspileM Unit := do
    -- dbg_trace s!">> appendDecl\n{ppDecl decl}\n"
    let ⟨name, _, _, params, value, _, _, _⟩ := decl
    visit name
    let ⟨params⟩ := params.map fun p => p.fvarId.name.toString false
    let value : Expr ← mkCode value
    let body := if params.isEmpty
      then value
      else mkLambda params value
    appendBinding (name, body)

  partial def appendMutualDecls (decls : List Decl) : TranspileM Unit := do
    -- dbg_trace s!">> appendMutualDecls"
    for decl in decls do
      visit decl.name
    let decls ← decls.mapM fun decl => do
      -- dbg_trace ppDecl decl
      let ⟨name, _, _, params, value, _, _, _⟩ := decl
      let ⟨params⟩ := params.map fun p => p.fvarId.name.toString false
      let value : Expr ← mkCode value
      let body := if params.isEmpty
        then value
        else mkLambda params value
      return (name.toString, body) -- TODO FIXME: this is pretty dangerous `toString`
    Expr.mkMutualBlock decls |>.forM
      fun (n, e) => appendBinding (n, e)

  partial def appendName (name : Name) : TranspileM Unit := do
    if (← get).visited.contains name then
      return
    -- dbg_trace s!">> appendName new name {name}"
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
        appendDecl $ ← getDecl name
      else
        -- TODO FIXME: no support for mutual overrides
        appendMutualDecls $ ← names.mapM getDecl

  partial def appendOverride (name : Name) : TranspileM Bool := do
    -- dbg_trace s!">> appendOverride {name}"
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
    appendPrereqs (x : Expr) : TranspileM Unit := do
      -- dbg_trace s!">> appendPrereqs {x.getFreeVars default default |>.toList}"
      x.getFreeVars default default |>.toList.forM fun n => do
        let n := n.toNameSafe
        if !(← isVisited n) then appendName n

end

/-- Main translation function -/
def transpileM (decl : Lean.Name) : TranspileM Unit :=
  let overrides := .ofList <| Lurk.Overrides.All.module.map fun o => (o.name, o)
  withOverrides overrides do
    -- dbg_trace s!">> transpileM overrides: {(← read).overrides.toList.map Prod.fst}"
    preloads.forM fun (name, preload) => do
      visit name
      appendBinding (name, preload) false
    appendName decl

/--
Constructs a `Expr.letRecE` whose body is the call to a `decl` constant in
a context and whose bindings are the constants in the context (including `decl`)
that are needed to define `decl`.
-/
def transpile (filePath : System.FilePath) (decl : Name) :
    IO $ Except String Expr := do
  let filePathStr := filePath.toString
  Lean.setLibsPaths
  match ← Lean.runFrontend (← IO.FS.readFile filePath) filePathStr with
  | (some err, _) => return .error err
  | (none, leanEnv) =>
    let transpileEnv := ⟨leanEnv, .empty⟩
    match TranspileM.run transpileEnv default (transpileM decl) with
    | .ok _ s =>
      let bindings := s.appendedBindings.data.map
        fun (n, x) =>
          (n.toString false, x)
      let expr := mkLetrec bindings (.sym $ decl.toString false)
      let expr := expr.pruneBlocks
      -- dbg_trace s!"{expr}"
      return .ok expr
    | .error e _ => .error e

end Yatima.Transpiler
