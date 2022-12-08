import Lean
import Std.Data.List.Basic
import Lurk.Syntax.ExprUtils
import Lurk.Evaluation.FromAST
import Yatima.Transpiler2.PP
import Yatima.Transpiler2.Compile
import Yatima.Transpiler2.LurkFunctions

namespace Yatima.Transpiler2

open Lurk.Syntax AST DSL
open Lean Compiler.LCNF

def overrides : List Override := [
  Lurk.Overrides2.Nat,
  Lurk.Overrides2.NatAdd,
  Lurk.Overrides2.NatMul,
  Lurk.Overrides2.NatDiv,
  Lurk.Overrides2.NatDecLe,
  Lurk.Overrides2.NatBeq,
  Lurk.Overrides2.Char,
  -- Lurk.Overrides2.CharMk,
  -- Lurk.Overrides2.CharVal,
  -- Lurk.Overrides2.CharValid,
  -- Lurk.Overrides2.CharRec,
  Lurk.Overrides2.List,
  Lurk.Overrides2.ListBeq,
  -- Lurk.Overrides2.ListNil,
  -- Lurk.Overrides2.ListCons,
  -- Lurk.Overrides2.ListRec,
  -- Lurk.Overrides2.ListMap,
  -- Lurk.Overrides2.ListFoldl,
  Lurk.Overrides2.String,
  Lurk.Overrides2.StringLength
  -- Lurk.Overrides2.StringMk,
  -- Lurk.Overrides2.StringData,
  -- Lurk.Overrides2.StringRec,
  -- Lurk.Overrides2.StringAppend
]

def preloads : List (Name × AST) := [
  Lurk.Preloads2.getelem,
  Lurk.Preloads2.drop,
  Lurk.Preloads2.neq,
  Lurk.Preloads2.str_mk,
  Lurk.Preloads2.str_data,
  Lurk.Preloads2.str_append
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

instance [ToAST α] [ToAST β] : ToAST (α × β) where
  toAST x := ~[toAST x.1, toAST x.2]

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
    match (← read).constants.find? ctor with
    | some (.ctorInfo ctor) => return ctor
    | _ => throw s!"malformed environment, {ctor} is not a constructor or doesn't exist"
  let ctorData := ctors.foldl (init := .empty)
    fun acc ctor => acc.insert ctor.name ctor.cidx
  appendInductiveData ⟨name, params, indices, ctorData⟩
  appendBinding (name, ← mkIndLiteral ind)
  for ctor in ctors do
    appendConstructor ctor

def getInductive (name : Name) : TranspileM InductiveVal := do
  match (← read).constants.find? name with
  | some (.inductInfo ind) => return ind
  | _ => throw s!"{name} is not an inductive"

def getCtorOrIndInfo? (name : Name) : TranspileM $ Option (List Name) := do
  match (← read).constants.find? name with
  | some (.inductInfo ind) => return some ind.all
  | some (.ctorInfo ctor) =>
    let ind ← getInductive ctor.induct
    return some ind.all
  | _ => return none

def appendCtorOrInd (name : Name) : TranspileM Bool := do
  match (← read).constants.find? name with
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

def mkFVarId : FVarId → TranspileM AST
  | fvarId => do mkName $ ← getBinderName fvarId

def mkArg : Arg → TranspileM AST
  | .erased => return toAST "lcErased"
  | .fvar fvarId => mkFVarId fvarId
    -- TODO: Hopefully can erase types??
  | .type _ => return toAST "lcErasedType"

def mkParam : Param → TranspileM AST
  | ⟨fvarId, binderName, type, borrow⟩ =>
    mkName binderName

def mkParams (params : Array Param) : TranspileM (Array AST) := do
  params.mapM mkParam

def mkCasesCore (indData : InductiveData) (discr : AST) (alts : Array Override.Alt) :
    TranspileM AST := do
  let mut defaultElse : AST := .nil
  let mut ifThens : Array (AST × AST) := #[]
  for alt in alts do match alt with
    | .default k => defaultElse := k
    | .alt cidx params k =>
      dbg_trace s!">> mkCases params: {params}, code: {k}"
      if params.isEmpty then
        ifThens := ifThens.push (⟦(= _lurk_idx $cidx)⟧, k)
      else
        let params : List (AST × AST) ← params.toList.enum.mapM fun (i, param) => do
            pure (← mkName param, ⟦(getelem _lurk_args $i)⟧)
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
    | .proj typeName idx struct =>
      -- TODO FIXME: use `typeName` to get params and add to `idx`
      return ⟦(getelem $idx $struct.name)⟧
    | .const declName _ args => do
      appendName declName
      if args.isEmpty then
        return toAST declName
      else
        return (toAST declName).cons $ toAST (← args.mapM mkArg)
    | .fvar fvarId args =>
      return (← mkFVarId fvarId).cons $ toAST (← args.mapM mkArg)

  partial def mkLetDecl : LetDecl → TranspileM AST
    | ⟨fvarId, binderName, type, value⟩ => do
      let binderName ← safeName binderName
      dbg_trace s!">> mkLetDecl {binderName} {← ppLetValue value}"
      let value ← mkLetValue value
      dbg_trace s!">> mkLetDecl {binderName} {value}"
      return ⟦($binderName $value)⟧

  partial def mkFunDecl : FunDecl → TranspileM AST
    | ⟨fvarId, binderName, params, type, value⟩ => do
      let binderName ← safeName binderName
      let value ← mkCode value
      let params ← params.mapM mkParam
      return ⟦($binderName (lambda $params $value))⟧

  partial def mkOverrideAlt (indData : InductiveData) :
      Alt → TranspileM Override.Alt
    | .default k => .default <$> mkCode k
    | .alt ctor params k => do
      let some cidx := indData.ctors.find? ctor |
        throw s!"{ctor} not a valid constructor for {indData.name}"
      let params ← params.mapM fun p => safeName p.binderName
      return .alt cidx params (← mkCode k)

  partial def mkOverrideAlts (indData : InductiveData) (alts : Array Alt) :
      TranspileM (Array Override.Alt) := do
    alts.mapM $ mkOverrideAlt indData

  partial def mkCases (cases : Cases) : TranspileM AST := do
    let ⟨typeName, resultType, discr, alts⟩ := cases
    appendName typeName
    let indData := ← match (← get).inductives.find? typeName with
      | some data => return data
      | none => throw s!"{typeName} is not an inductive"
    let discr ← mkFVarId discr
    let alts ← mkOverrideAlts indData alts
    match (← read).overrides.find? typeName with
    | some (.ind ind) => liftExcept <| ind.mkCases discr alts
    | none => mkCasesCore indData discr alts
    | some (.decl _) => throw s!"found a declaration override for {typeName}"

  partial def mkCode : Code → TranspileM AST
    | .let decl k => do
      dbg_trace s!">> mkCode let decl: {← ppLetDecl decl}, k: {← ppCode k}"
      let decl ← mkLetDecl decl
      let k ← mkCode k
      dbg_trace s!">> mkCode let decl: {decl}, k: {k}"
      return ⟦(let ($decl) $k)⟧
    | .fun decl k => do
      dbg_trace s!">> mkCode fun decl: {← ppFunDecl decl}, k: {← ppCode k}"
      let decl ← mkFunDecl decl
      let k ← mkCode k
      dbg_trace s!">> mkCode fun decl: {decl}, k: {k}"
      return ⟦(let ($decl) $k)⟧
    | .jp decl k => do
      dbg_trace s!">> mkCode fun decl: {← ppFunDecl decl}, k: {← ppCode k}"
      let decl ← mkFunDecl decl
      let k ← mkCode k
      dbg_trace s!">> mkCode fun decl: {decl}, k: {k}"
      return ⟦(let ($decl) $k)⟧
    | .jmp fvarId args => do
      let fvarId ← mkFVarId fvarId
      let args ← args.mapM mkArg
      return .cons fvarId (toAST args)
    | .cases cases => mkCases cases
    | .return fvarId => mkFVarId fvarId
    | .unreach _ => return toAST "lcUnreachable"

  partial def appendDecl (decl : Decl) : TranspileM Unit := do
    dbg_trace s!">> appendDecl\n{← ppDecl decl}\n"
    let ⟨name, lvls, type, params, value, recr, safe, inlineAttr?⟩ := decl
    visit name
    let params : Array AST := params.map fun p => toAST p.binderName
    let value : AST ← mkCode value
    dbg_trace s!">> appendDecl value: {value}\n"
    let body := if params.isEmpty
      then value
      else ~[.sym "LAMBDA", toAST params, value]
    appendBinding (name, body)

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
      if ← appendOverride name then
        return
      match (← read).decls.find? name with
      | some decl => appendDecl decl
      | none => throw s!"decls does not contain {name}"

  partial def appendOverride (name : Name) : TranspileM Bool := do
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
    appendPrereqs : AST → TranspileM Unit
      | .num _ | .char _ | .str _ => return
      | .cons e₁ e₂ => do appendPrereqs e₁; appendPrereqs e₂
      | .sym n => do
        if !(reservedSyms.contains n) && !(← isVisited n) then
          if (← read).decls.contains name then
            appendName n

end

/-- Main translation function -/
def transpileM (root : Lean.Name) : TranspileM Unit :=
  let overrides := .ofList <| overrides.map fun o => (o.name, o)
  withOverrides overrides do
    dbg_trace s!">> transpileM overrides: {(← read).overrides.toList.map Prod.fst}"
    for (name, preload) in preloads do
      visit name
      appendBinding (name, preload) false
    appendName root

/--
Constructs a `AST.letRecE` whose body is the call to a `root` constant in
a context and whose bindings are the constants in the context (including `root`)
that are needed to define `root`.
-/
def transpile (env : TranspileEnv) (root : Lean.Name) :
    Except String Lurk.Evaluation.Expr := do
  match TranspileM.run env default (transpileM root) with
  | .ok _ s =>
    let bindings := s.appendedBindings.data.map
      fun (n, x) =>
        dbg_trace s!">> transpile {n}: {x}"
        (n.toString false, x)
    let ast := mkLetrec bindings (.sym $ root.toString false)
    let ast ← ast.pruneBlocks
    dbg_trace s!">> transpile result:\n{ast}\n"
    ast.toExpr
  | .error e _ => .error e

end Yatima.Transpiler2
