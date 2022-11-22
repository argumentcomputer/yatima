import Yatima.Transpiler2.Simp
import Yatima.Transpiler2.TranspileM
import Yatima.Transpiler2.LurkFunctions
import Yatima.Transpiler2.Utils
import Lurk.Syntax.ExprUtils

namespace Yatima.Transpiler

open IR Lurk.Syntax AST DSL

/-- Initialize builtin lurk constants defined in `LurkFunctions.lean` -/
def overrides : List (Name × AST) := [
  Lurk.Overrides.Nat,
  Lurk.Overrides.NatZero,
  Lurk.Overrides.NatSucc,
  Lurk.Overrides.NatRec,
  Lurk.Overrides.NatAdd,
  Lurk.Overrides.NatMul,
  Lurk.Overrides.NatDiv,
  Lurk.Overrides.NatDecLe,
  Lurk.Overrides.NatBeq,
  Lurk.Overrides.Char,
  Lurk.Overrides.CharMk,
  Lurk.Overrides.CharVal,
  Lurk.Overrides.CharValid,
  Lurk.Overrides.CharRec,
  -- Lurk.Overrides.List,
  -- Lurk.Overrides.ListNil,
  -- Lurk.Overrides.ListCons,
  -- Lurk.Overrides.ListRec,
  -- Lurk.Overrides.ListMap,
  -- Lurk.Overrides.ListFoldl,
  Lurk.Overrides.String,
  Lurk.Overrides.StringMk,
  Lurk.Overrides.StringData,
  Lurk.Overrides.StringRec,
  Lurk.Overrides.StringAppend
]

def preloads : List (Name × AST) := [
  Lurk.Preloads.getelem,
  Lurk.Preloads.str_mk,
  Lurk.Preloads.str_data,
  Lurk.Preloads.str_append
]

def preloadNames : Lean.NameSet :=
  .ofList (preloads.map Prod.fst)

def safeName (name : Name) : TranspileM Name :=
  let nameStr := name.toString false
  if name.isHygenic
      || preloadNames.contains name
      || reservedSyms.contains nameStr
      || nameStr.contains '|' then do
    match (← get).replaced.find? name with
    | some n => return n
    | none   => replace name
  else return name

def mkName (name : Name) : TranspileM AST := do
  toAST <$> safeName name

def appendBinding (b : Name × AST) (safe := true) : TranspileM Unit := do
  let b := if safe then (← safeName b.1, b.2) else b
  modify fun stt => { stt with appendedBindings := stt.appendedBindings.push b }

def mkIndLiteral (ind : Both Inductive) (indLit : AST) : TranspileM AST := do
  let type ← derefExpr ⟨ind.anon.type, ind.meta.type⟩
  match (← read).store.telescopeLamPi #[] type with
  | some (#[], _) => return indLit
  | some (as,  _) => return ⟦(lambda $as $indLit)⟧
  | none => throw ""

/-- TODO explain this; `p` is `params`, `i` is `indices` -/
def splitCtorArgs (args : List AST) (p i : Nat) : List (List AST) :=
  let (params, rest) := args.splitAt p
  let (indices, args) := rest.splitAt i
  [params, indices, args]

def appendCtor (ctor : Both Constructor) (indLit : AST) (indices : Nat) :
    TranspileM Unit := do
  let type ← derefExpr ⟨ctor.anon.type, ctor.meta.type⟩
  let name := ctor.meta.name.projᵣ
  let idx := ctor.anon.idx.projₗ
  match (← read).store.telescopeLamPi #[] type with
  | some (#[], _) => appendBinding (name, mkConsList [indLit, .num idx])
  | some (as,  _) =>
    let ctorArgs ← as.data.mapM mkName
    let ctorData := splitCtorArgs ctorArgs ctor.anon.params.projₗ indices
    let ctorDataAST := ctorData.map mkConsList
    let ctorData := mkConsList (indLit :: .num idx :: ctorDataAST)
    appendBinding (name, ⟦(lambda $ctorArgs $ctorData)⟧)
  | none => throw ""

scoped instance [ToAST α] [ToAST β] : ToAST (α × β) where
  toAST x := ~[toAST x.1, toAST x.2]

mutual

partial def mkRecursor (recr : Both $ Recursor r) (rhs : List $ Both Constructor) :
    TranspileM $ String × AST := do
  let recrType ← derefExpr ⟨recr.anon.type, recr.meta.type⟩
  match (← read).store.telescopeLamPi #[] recrType with
  | none => throw ""
  | some (as, _) => match as.data.reverse with
    | [] => throw ""
    | argName :: _ =>
      let argName ← safeName argName
      let recrArgs ← as.data.mapM mkName
      let recrIndices := recr.anon.indices.projₗ
      let store := (← read).store
      let ifThens : List (AST × AST) ← rhs.mapM fun ctor => do
        let (idx, fields) := (ctor.anon.idx.projₗ, ctor.anon.fields.projₗ)
        let rhs ← derefExpr ⟨ctor.anon.rhs, ctor.meta.rhs⟩
        match store.telescopeLamPi #[] rhs with
        | none => throw ""
        | some (as, rhs) =>
          let rhs ← mkAST rhs
          let _lurk_ctor_args := ⟦(getelem (cdr (cdr $argName)) 2)⟧
          let ctorArgs := (List.range fields).map
            fun (n : Nat) => ⟦(getelem _lurk_ctor_args $n)⟧

          let rhsCtorArgNames := as.data.takeLast (fields - recrIndices)
          let rhsCtorArgNames ← rhsCtorArgNames.mapM mkName

          let bindings := (AST.sym "_lurk_ctor_args", _lurk_ctor_args) ::
            rhsCtorArgNames.zip ctorArgs

          -- extract snd element
          pure (⟦(= (car (cdr $argName)) $idx)⟧, ⟦(let $bindings $rhs)⟧)
      let cases := AST.mkIfElses ifThens .nil
      return (recr.meta.name.projᵣ.toString false, ⟦(lambda $recrArgs $cases)⟧)

partial def overrideWith (name : Name) (func : AST) : TranspileM Unit := do
  visit name
  appendPrereqs func
  appendBinding (name, func)
where
  appendPrereqs : AST → TranspileM Unit
    | .num _ | .char _ | .str _ => return
    | .cons e₁ e₂ => do appendPrereqs e₁; appendPrereqs e₂
    | .sym n => do
      if !(reservedSyms.contains n) && !(← isVisited n) then
        match (← read).map.find? n with
        | some const => appendConst const
        | none => return

partial def mkAST : Both Expr → TranspileM AST
  | ⟨.sort .., .sort  ..⟩ => return .nil -- TODO?
  | ⟨.var  .., .var n ..⟩ => mkName n.projᵣ
  | ⟨.const _ anon _, .const n meta _⟩ => do
    let name := n.projᵣ
    if !(← isVisited name) then
      match (← read).overrides.find? name with
      | some ast => overrideWith name ast
      | none => appendConst $ ← derefConst ⟨anon, meta⟩
    mkName name
  | ⟨.app fAnon aAnon, .app fMeta aMeta⟩ => do -- TODO : flatten
    let f ← derefExpr ⟨fAnon, fMeta⟩
    let a ← derefExpr ⟨aAnon, aMeta⟩
    pure ~[← mkAST f, ← mkAST a]
  | e@⟨.pi  .., .pi  ..⟩
  | e@⟨.lam .., .lam ..⟩ => do match (← read).store.telescopeLamPi #[] e with
    | some (as, b) =>
      let as ← as.mapM safeName
      let b ← mkAST b
      return ⟦(lambda $as $b)⟧
    | _ => throw ""
  | e@⟨.letE .., .letE ..⟩ => do match (← read).store.telescopeLetE #[] e with
    | some (bs, b) =>
      let bs ← bs.data.mapM fun (n, v) => do
        pure (toString $ ← safeName n, ← mkAST v)
      return .mkLet bs (← mkAST b)
    | _ => throw ""
  | ⟨.lit l, .lit _⟩ => match l.projₗ with
    | .natVal n => return ⟦$n⟧
    | .strVal s => return ⟦$s⟧
  | ⟨.proj idx eAnon, .proj _ eMeta⟩ => do
    -- this is very nifty; `e` contains its type information *at run time*
    -- which we can take advantage of to compute the projection
    let e ← mkAST $ ← derefExpr ⟨eAnon, eMeta⟩
    let args := ⟦(getelem (cdr (cdr $e)) 2)⟧
    return ~[.sym "getelem", args, .num idx.projₗ]
  | _ => throw ""

partial def appendConst (c : Both Const) : TranspileM Unit := do
  let constName := c.meta.name
  if ← isVisited constName then return
  visit constName
  match c with
  | ⟨.axiom _, .axiom _⟩
  | ⟨.quotient _, .quotient _⟩ => return
  | ⟨.theorem anon, .theorem meta⟩
  | ⟨.opaque anon, .opaque meta⟩ =>
    appendBinding (constName, ← mkAST (← derefExpr ⟨anon.value, meta.value⟩))
  | ⟨.definitionProj anon, .definitionProj meta⟩ =>
    match ← derefDefBlock ⟨anon.block, meta.block⟩ with
    | [d] => appendBinding (constName, ← mkAST (← derefExpr ⟨d.anon.value, d.meta.value⟩))
    | ds  =>
      ds.forM fun d => visit d.meta.name.projᵣ
      let pairs ← ds.mapM fun d => do
        pure (
          d.meta.name.projᵣ.toString false,
          ← mkAST $ ← derefExpr ⟨d.anon.value, d.meta.value⟩)
      match mkMutualBlock pairs with
      | .ok block => block.forM fun (n, e) => appendBinding (n, e)
      | .error err => throw err
  | ⟨.inductiveProj   anon, .inductiveProj   meta⟩
  | ⟨.constructorProj anon, .constructorProj meta⟩
  | ⟨.recursorProj    anon, .recursorProj    meta⟩ =>
    for ind in ← derefIndBlock ⟨anon.block, meta.block⟩ do
      let indAnon := ind.anon
      let indMeta := ind.meta
      let indName := indMeta.name.projᵣ
      let indices := ind.anon.indices.projₗ
      let indLit := ⟦,($(indName.toString false) $ind.anon.params.projₗ $indices)⟧
      visit indName
      appendBinding (indName, ← mkIndLiteral ind indLit)
      let ctors := (indAnon.ctors.zip indMeta.ctors).map fun (a, m) => ⟨a, m⟩
      for ctor in ctors do
        visit ctor.meta.name.projᵣ
        appendCtor ctor indLit indices
      let mut recrs := []
      for pair in indAnon.recrs.zip indMeta.recrs do
        let meta := Sigma.snd pair.2
        visit meta.name.projᵣ
        if h : Sigma.fst pair.2 = Sigma.fst pair.1 then
          let x := ⟨Sigma.snd pair.1, by rw [h] at meta; exact meta⟩
          recrs := (← mkRecursor x ctors) :: recrs
        else throw ""
      match mkMutualBlock recrs with
      | .ok xs => xs.forM fun (n, e) => appendBinding (n, e)
      | .error e => throw ""
  | _ => throw ""

end

/-- Main translation function -/
def transpileM (root : Name) : TranspileM Unit := do
  preloads.forM (appendBinding · false)
  match (← read).map.find? root with
  | some c => appendConst c
  | none => throw s!"Unknown const {root}"

/--
Constructs a `letrec` block whose body is the call to a `root` constant in
a context and whose bindings are the constants in the context (including `root`)
that are needed to define `root`.
-/
def transpile (store : Store) (root : String) : Except String AST := do
  let map ← store.consts.foldlM (init := default) fun acc cid =>
    match store.getConst? cid with
    | some c => pure $ acc.insert c.meta.name c
    | _ => throw ""
  let env := ⟨store, map, .ofList overrides _⟩
  let stt := ⟨#[], .empty, ⟨"_x", 1⟩, .empty⟩
  match StateT.run (ReaderT.run (transpileM root) env) stt with
  | (.error err, _) => throw err
  | (.ok _, stt) =>
    let bindings := stt.appendedBindings.data.map
      fun (n, x) => (n.toString false, x)
    let ast := Simp.simp $ mkLetrec bindings (.sym root)
    ast.pruneBlocks

end Yatima.Transpiler
