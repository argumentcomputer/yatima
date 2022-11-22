import Yatima.Transpiler2.Simp
import Yatima.Transpiler2.TranspileM
import Yatima.Transpiler2.LurkFunctions
import Yatima.Transpiler2.Utils
import Lurk.Syntax.ExprUtils

/-!
# The Transpiler

This file provides all core functions needed to build Lurk expressions from raw
Yatima IR.

For many functions, we choose to return `TranspileM Unit` instead of
`TranspileM AST`. This may be slightly strange as the naming suggests that we
are producing Lurk expressions, but the final action is binding the transpiled
result into the Lurk output, so `Unit` is often more natural to return.

## Inductives

Currently, inductives encode three pieces of information.
1. The name of the inductive. This is not used anywhere in the transpiler,
   but is useful to keep around for humans to debug and identify objects.
2. The number of parameters. Used to generate projections.
3. The number of indices. Also used to generate projections.

This information is somewhat arbitrary. It's the bare minimum needed to
make things work. If there are better representations or we need more
metadata it should be freely changed.

For example, the definition of `Nat` is (the comma is the Lurk `quote`)
```
,("Nat" 0 0)
```

For inductives with parameters and indices, we must encode the definitions
as functions. When types are not erased, inductive types
must be treated as meaningful functions. For example, `Prod` is
```
(lambda (:1 :2) ,("Prod" 2 0))
```

If types are erased, then these parameters and indices may be ignored.
Perhaps with erased types, a different inductive representation could be used.

## Constructors

See the docstring for `ctorToLurkExpr`. Here are some examples:
1. `Nat`
  a. `Nat.zero` is `(Nat 0)`
  b. `Nat.succ` is `(lambda n => (Nat 1 n))`

So `2` is `(Nat 1 Nat 1 Nat 0)`.
This clearly duplicates `Nat` a lot, so we should try to find an
more compact representation for constructor/inductive data.

2. `Prod`
  a. `Prod.mk` is `(lambda (α β fst snd) ((Prod α β) 0 α β fst snd))`

Note that `(Prod α β)` reduces to `("Prod" 2 0)`, allowing us to access
the inductive data.

## Recursors

See the docstrings for `intRecrToLurkExpr` and `extRecrToLurkExpr`.
Here are some examples:

TODO

## Projections

Yatima projections are encoded by `.proj idx e`, where `e` is the expression
and `idx` is the index of the data we want to extract out of `e`.

Recall that we encode inductive constructors with a list: `ctorᵢ a₁ a₂ ..`.
In particular, structures only have one constructor: `struct.mk`, and their
data is simply recorded in a list. Hence, one may think that we can simply
write `getelem e (idx + 2)` (the `+2` is to skip the name and constructor index).

However! This fails because structures may have parameters. For example,
the tuple `(1, 2)` is encoded in Lurk as `e := ((Prod Nat Nat) 0 Nat Nat 1 2)`.
If we want `e.1`, then `getelem e (1 + 2)` is `Nat`. In general, constructor
arguments will always first contain the parameters and indices, before the
actual fields of the constructor. So we modify our first solution to include
these. `let args := cdr (cdr e) in getelem args (idx + params + indices)`.

Great! Now how do we find `params` and `indices`? We can simply look at the
head of `e`: since `e` is an inductive, we know that the head holds some
inductive type `((<ind> <args>) <params> <indices>)`! This is the reason we
include the two `params` and `indices` in the inductive data.

Note that because we don't know what the head of `e` is until we reduce it,
this logic occurs *at run time*!

# Example: Three
inductive Three where
  | A : Three
  | B : Three
  | C : Three

## Translated Lurk Constructors

`Three.A`:
`["Three", 0]`

`Three.B`:
`["Three", 1]`

`Three.C`:
`["Three", 2]`

## Recursor
Three.rec :
  {motive : Three → Sort u} →
  motive Three.A →
  motive Three.B →
  motive Three.C →
  (t : Three) →
  motive t

## Reduction Rules

Three.rec {P} caseA caseB caseC Three.A = caseA
Three.rec {P} caseA caseB caseC Three.B = caseB
Three.rec {P} caseA caseB caseC Three.C = caseC

## Translated Lurk Recursor

`Three.rec`:
lambda motive caseA caseB caseC three,
  if three.cidx == 0
    return caseA
  else if three.cidx == 1
    return caseB
  else if three.cidx == 2
    return caseC

# Nat

## Reduction Rules
Nat.rec {P} caseZero caseSucc Nat.zero = caseZero
Nat.rec {P} caseZero caseSucc (Nat.succ n) =
  caseSucc n (Nat.rec {P} caseZero caseSucc n)

## Translated Lurk Constructors

`Nat.zero`:
`["Nat", 0]`

`Nat.succ`:
`lambda n, ["Nat", 1, n]`

### Yatima Compiled Reduction Rules
Nat.zero 0
λ (motive : Nat.0 -> (Sort)) (zero : motive.0 Nat.zero.2) (succ : Π (a._@._hyg.4 : Nat.2), (motive.2 a._@._hyg.4.0) -> (motive.3 (Nat.succ.6 a._@._hyg.4.1)))
  => zero.1
Nat.succ 1
λ (motive : Nat.0 -> (Sort)) (zero : motive.0 Nat.zero.2) (succ : Π (a._@._hyg.4 : Nat.2), (motive.2 a._@._hyg.4.0) -> (motive.3 (Nat.succ.6 a._@._hyg.4.1))) (a._@._hyg.4 : Nat.3)
  => succ.1 a._@._hyg.4.0 (Nat.rec.7 motive.3 zero.2 succ.1 a._@._hyg.4.0)

## Translated Lurk Recursor
lambda motive caseZero caseSucc n,
  if n.cidx == 0
    caseZero
  else if n.cidx == 1
    caseSucc n (Nat.rec motive caseZero caseSucc n.args)

# Vector

inductive Vector (A : Type) : (n : Nat) → Type where
  | nil : Vector A 0
  | cons : {n : Nat} → (a : A) → (as : Vector A n) → Vector A (n+1)

## Translated Lurk Constructors
`Vector.nil`:
`["Vector", 0]`

`Vector.cons`:
`lambda n a as, ["Vector", 1, n, a, as]`

## Reduction Rules

Vector.rec {A} {P} caseNil caseCons {m} (Vector.nil {A}) = caseNil     -- where m must be equal to 0
Vector.rec {A} {P} caseNil caseCons {m} (Vector.cons {A} {n} a as) =   -- where m must be equal n+1
  caseCons {n} a as (Vector.rec {A} {P} caseNil caseCons {n} as)

### Yatima Compiled Reduction Rules

Vector.nil 0
λ (A : Sort)
  (motive : Π (n : Nat),
  (Vector.2 A.1 n.0) -> (Sort))
  (nil : motive.0 Nat.zero (Vector.nil.3 A.1))
  (cons : Π {n : Nat} (a : A.3) (as : Vector.5 A.4 n.1), (motive.4 n.2 as.0) -> (motive.5 (Nat.succ n.3) (Vector.cons.9 A.6 n.3 a.2 as.1)))
  => nil.1
Vector.cons 3
λ (A : Sort)
  (motive : Π (n : Nat),
  (Vector.2 A.1 n.0) -> (Sort))
  (nil : motive.0 Nat.zero (Vector.nil.3 A.1))
  (cons : Π {n : Nat} (a : A.3) (as : Vector.5 A.4 n.1), (motive.4 n.2 as.0) -> (motive.5 (Nat.succ n.3) (Vector.cons.9 A.6 n.3 a.2 as.1))) {n : Nat} (a : A.4) (as : Vector.6 A.5 n.1)
  => cons.3 n.2 a.1 as.0 (Vector.rec.10 A.6 motive.5 nil.4 cons.3 n.2 as.0)

## Translated Lurk Recursor
`Vector.rec`:
lambda A motive caseNil caseCons m `v`,
if `v`.cidx == 0
  caseNil
else if `v`.cidx == 1
  (n, a, as) ← `v`.args
  caseCons n a as (Vector.rec A motive caseNil caseCons n as)
-/

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

def telescopeLamPi (e : Both Expr) : TranspileM $ (Array Name) × Both Expr := do
  match (← read).store.telescopeLamPi #[] e with
  | some x => pure x
  | none => throw "Error when telescoping lambda or pi"

def mkIndLiteral (ind : Both Inductive) (indLit : AST) : TranspileM AST := do
  let type ← derefExpr ⟨ind.anon.type, ind.meta.type⟩
  let as ← (← telescopeLamPi type).1.mapM safeName
  if as.isEmpty then return indLit
  else return ⟦(lambda $as $indLit)⟧

/-- TODO explain this; `p` is `params`, `i` is `indices` -/
def splitCtorArgs (args : List Name) (p i : Nat) : List (List Name) :=
  let (params, rest) := args.splitAt p
  let (indices, args) := rest.splitAt i
  [params, indices, args]

def appendCtor (ctor : Both Constructor) (indLit : AST) (indices : Nat) :
    TranspileM Unit := do
  let type ← derefExpr ⟨ctor.anon.type, ctor.meta.type⟩
  let name := ctor.meta.name.projᵣ
  let idx := ctor.anon.idx.projₗ
  let as := (← telescopeLamPi type).1
  if as.isEmpty then
    appendBinding (name, mkConsList [indLit, .num idx])
  else
    let ctorArgs ← as.data.mapM safeName
    let ctorData := splitCtorArgs ctorArgs ctor.anon.params.projₗ indices
    let ctorData := ctorData.map (·.map toAST)
    let ctorDataAST := ctorData.map mkConsList
    let ctorData := mkConsList (indLit :: .num idx :: ctorDataAST)
    appendBinding (name, ⟦(lambda $ctorArgs $ctorData)⟧)

/--
Transforms a list of named expressions that were mutually defined into a
"switch" function `S` and a set of projections (named after the original names)
that call `S` with their respective indices.
-/
def mkMutualBlock : List (Name × AST) → Except String (List $ Name × AST)
  | [] => throw "can't make a mutual block with an empty list of binders"
  | x@([_]) => return x
  | mutuals => do
    let names := mutuals.map Prod.fst
    let mutualName := names.foldl (fun acc n => acc ++ n) `__mutual__
    let fnProjs := names.enum.map fun (i, n) => (n, ⟦($mutualName $i)⟧)
    let map := fnProjs.foldl (init := default)
      fun acc (n, e) => acc.insert (n.toString false) e
    let ifThens ← mutuals.enum.mapM
      fun (i, _, e) => do pure (⟦(= mutidx $i)⟧, ← replaceFreeVars map e)
    let mutualBlock := mkIfElses ifThens
    return (mutualName, ⟦(lambda (mutidx) $mutualBlock)⟧) :: fnProjs

mutual

partial def mkRecursor (recr : Both $ Recursor r) (ctors : List $ Both Constructor) :
    TranspileM $ Name × AST := do
  let recrType ← derefExpr ⟨recr.anon.type, recr.meta.type⟩
  match ← telescopeLamPi recrType with
  | (as, _) => match as.data.reverse with
    | [] => throw "Empty arguments for recursor type"
    | argName :: _ =>
      let argName ← safeName argName
      let recrArgs ← as.mapM safeName
      let recrIndices := recr.anon.indices.projₗ
      let ifThens : List (AST × AST) ← ctors.mapM fun ctor => do
        let (idx, fields) := (ctor.anon.idx.projₗ, ctor.anon.fields.projₗ)
        let rhs ← derefExpr ⟨ctor.anon.rhs, ctor.meta.rhs⟩
        let (as, rhs) ← telescopeLamPi rhs
        let rhs ← mkAST rhs
        let _lurk_ctor_args := ⟦(getelem (cdr (cdr $argName)) 2)⟧
        let ctorArgs := (List.range fields).map
          fun (n : Nat) => ⟦(getelem _lurk_ctor_args $n)⟧

        let rhsCtorArgNames := as.data.takeLast (fields - recrIndices)

        let bindings :=
          (`_lurk_ctor_args, _lurk_ctor_args) :: rhsCtorArgNames.zip ctorArgs
          |>.map fun (n, e) => (n.toString false, e)

        -- extract snd element
        pure (⟦(= (car (cdr $argName)) $idx)⟧, .mkLet bindings rhs)
      let cases := AST.mkIfElses ifThens .nil
      return (recr.meta.name.projᵣ, ⟦(lambda $recrArgs $cases)⟧)

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
  | e@⟨.app .., .app ..⟩ => do match (← read).store.telescopeApp [] e with
    | some as =>
      let as ← as.mapM mkAST
      return consWith as .nil
    | none => throw "Error when telescoping app"
  | e@⟨.pi  .., .pi  ..⟩
  | e@⟨.lam .., .lam ..⟩ => do
    let (as, b) ← telescopeLamPi e
    let as ← as.mapM safeName
    let b ← mkAST b
    return ⟦(lambda $as $b)⟧
  | e@⟨.letE .., .letE ..⟩ => do match (← read).store.telescopeLetE #[] e with
    | some (bs, b) =>
      let bs ← bs.data.mapM fun (n, v) => do
        pure (toString $ ← safeName n, ← mkAST v)
      return .mkLet bs (← mkAST b)
    | _ => throw "Error when telescoping letE"
  | ⟨.lit l, .lit _⟩ => match l.projₗ with
    | .natVal n => return ⟦$n⟧
    | .strVal s => return ⟦$s⟧
  | ⟨.proj idx eAnon, .proj _ eMeta⟩ => do
    -- this is very nifty; `e` contains its type information *at run time*
    -- which we can take advantage of to compute the projection
    let e ← mkAST $ ← derefExpr ⟨eAnon, eMeta⟩
    let args := ⟦(getelem (cdr (cdr $e)) 2)⟧
    return ~[.sym "getelem", args, .num idx.projₗ]
  | _ => throw "Ill-formed expression"

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
    | [ ] => throw "Empty mutual definition block"
    | [d] => appendBinding (constName, ← mkAST (← derefExpr ⟨d.anon.value, d.meta.value⟩))
    | ds  =>
      ds.forM fun d => visit d.meta.name.projᵣ
      let pairs ← ds.mapM fun d => do
        let b ← mkAST $ ← derefExpr ⟨d.anon.value, d.meta.value⟩
        pure (d.meta.name.projᵣ, b)
      (← mkMutualBlock pairs).forM appendBinding
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
        else throw "Incompatible RecTypes between anon and meta data"
      (← mkMutualBlock recrs).forM appendBinding
  | _ => throw ""

end

/-- Main translation function -/
def transpileM (root : String) : TranspileM Unit := do
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
    | some c => pure $ acc.insert (c.meta.name.toString false) c
    | _ => throw "Couldn't retrieve constant from cid"
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
