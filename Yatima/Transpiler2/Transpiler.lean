import Yatima.Transpiler.Simp
import Yatima.Transpiler2.TranspileM
import Yatima.Transpiler.LurkFunctions
import Lurk.Syntax.ExprUtils

def Lean.Name.isHygenic : Name → Bool
  | str p s => if s == "_hyg" then true else p.isHygenic
  | num p _ => p.isHygenic
  | _       => false

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

def mkIndLiteral (ind : Both Inductive) : TranspileM AST := do
  sorry

def mkRecursor (recr : Both $ Recursor r) : TranspileM (String × AST) := sorry

mutual

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
  | ⟨.sort .., .sort  ..⟩ => return .nil -- TODO
  | ⟨.var  .., .var n ..⟩ => mkName n.projᵣ
  | ⟨.const _ anon _, .const n meta _⟩ => do
    let name := n.projᵣ
    match (← read).overrides.find? name with
    | some ast => overrideWith name ast
    | none => appendConst $ ← derefConst ⟨anon, meta⟩
    mkName name
  | e@⟨.app .., .app ..⟩ => do
    let store := (← read).store
    match (store.getAppFn e, store.getAppArgs #[] e) with
    | (some f, some as) =>
      let tail ← as.foldrM (init := .nil) fun e acc => do
        pure $ ~[← mkAST e, acc]
      return ~[← mkAST f, tail]
    | _ => throw ""
  | e@⟨.pi  .., .pi  ..⟩
  | e@⟨.lam .., .lam ..⟩ => do match (← read).store.telescopeLamPi #[] e with
    | some (as, b) =>
      let as ← as.mapM mkName
      let fn ← mkAST e
      return ⟦(lambda $as $fn)⟧
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
    return ⟦(getelem $args $idx.projₗ)⟧
  | _ => throw ""

partial def appendCtor (ctor : Both Constructor) : TranspileM Unit := sorry

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
    | [ ] => throw ""
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
      visit indName
      appendBinding (indName, ← mkIndLiteral ind)
      for ctor in (indAnon.ctors.zip indMeta.ctors).map fun (a, m) => ⟨a, m⟩ do
        visit ctor.meta.name.projᵣ
        appendCtor ctor
      let recrs ← (indAnon.recrs.zip indMeta.recrs).mapM fun pair => do
        let meta := Sigma.snd pair.2
        visit meta.name.projᵣ
        if h : Sigma.fst pair.2 = Sigma.fst pair.1 then
          let x := ⟨Sigma.snd pair.1, by rw [h] at meta; exact meta⟩
          mkRecursor x
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
