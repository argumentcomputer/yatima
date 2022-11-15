import Yatima.Converter.Converter
import Yatima.Transpiler.Simp
import Yatima.Transpiler.Utils
import Yatima.Transpiler.LurkFunctions
import YatimaStdLib.List
import Lurk.Syntax.ExprUtils

/-!
# The Transpiler

This file provides all core functions needed to build Lurk expressions from raw Yatima IR.

Each function takes some Yatima object and converts it to its lurk representation;
we follow the naming convention `<yatima-object>ToLurkExpr`.

For many functions, we choose to return `TranspileM Unit` instead of `TranspileM AST`.
This may be slightly strange as the naming suggests that we are producing Lurk expressions,
but the final action is binding the transpiled result into the Lurk output, so `Unit` is
often more natural to return.

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

open TC Lurk.Syntax AST DSL

def replaceName (name : Name) : TranspileM Name := do
  if name.isHygenic then
    match (← get).replaced.find? name with
    | some n => return n
    | none   => replaceFreshId name
  else return name

def mkName (name : Name) : TranspileM AST := do
  toAST <$> replaceName name

def mkIndLiteral (ind : Inductive) : TranspileM AST := do
  let (name, params, indices, type) := (toString ind.name, ind.params, ind.indices, ind.type)
  let (_, args) := telescope type
  let args : List Name ← args.mapM fun (n, _) => replaceName n
  if args.isEmpty then
    return ⟦,($name $params $indices)⟧
  else
    return ⟦(lambda ($args) ,($name $params $indices))⟧

/-- TODO explain this; `p` is `params`, `i` is `indices` -/
def splitCtorArgs (args : List AST) (p i : Nat) : List (List AST) :=
  let (params, rest) := args.splitAt p
  let (indices, args) := rest.splitAt i
  [params, indices, args]

scoped instance [ToAST α] [ToAST β] : ToAST (α × β) where 
  toAST x := ~[toAST x.1, toAST x.2]

mutual

  /-- Converts Yatima lambda `fun x₁ x₂ .. => body` into `AST.lam [x₁, x₂, ..] body` -/
  partial def mkLambda (expr : Expr) : TranspileM AST := do
    let (expr, binds) := telescope expr
    let binds : List Name ← binds.mapM fun (n, _) => replaceName n
    let fn ← mkLurkExpr expr
    return AST.mkLambda (binds.map fun n => n.toString false) fn

  /-- Construct a Lurk function representing a Yatima constructor.
    Let `ind` be the inductive parent of `ctor` and `idx` be its index.

    * Data (0-ary) constructors are represented as `((ind <params> <indices>) idx)`.
    * Function constructors are represented as
      `(lambda (a₁ a₂ ..) ((ind <params> <indices>) idx a₁ a₂ ..))`

    Recall that when `ind` has parameters and indices, it is represented as a function.
    Hence we must apply arguments to access the inductive data. This is required for
    projections.

    The `indices` argument is necessary since `Constructor` contains the
    `params` field of its parent's inductive, but not the `indices` field. -/
  partial def mkConstructor (ctor : Constructor) (indLit : AST) (indices : Nat) : TranspileM Unit := do
    let (name, idx, type) := (ctor.name, ctor.idx, ctor.type)
    let (_, bindings) := telescope type
    let ctorArgs : List Name ← bindings.mapM fun (n, _) => replaceName n
    let ctorData := splitCtorArgs (← ctorArgs.mapM mkName) ctor.params indices
    let ctorDataAST := ctorData.map fun x => consWith x .nil
    let ctorData := consWith (indLit :: ⟦$idx⟧ :: ctorDataAST) .nil
    let body := if ctorArgs.isEmpty then
      ⟦(cons $indLit (cons $idx nil))⟧
    else
      ⟦(lambda ($ctorArgs) $ctorData)⟧
    appendBinding (name, body)

  partial def mkListRecursor (recrType : Expr) (recrName : Name) (rhs : List Constructor) :
      TranspileM (String × AST) := do
    let (_, bindings) := telescope recrType
    let (argName, _) : Name × Expr := bindings.last!
    let recrArgs : List Name ← bindings.mapM fun (n, _) => replaceName n
    let mut [(n₁, rhs₁), (n₂, rhs₂)] ← rhs.mapM fun c => return (c.name, c.rhs)
      | throw $ .custom "`mkListRecursor` must receive list constructors"
    let (nilRHS, consRHS) :=
      if n₁ == ``List.nil then (rhs₁, rhs₂)
      else (rhs₂, rhs₁)
    let nilRHS ← mkLurkExpr nilRHS.toImplicitLambda
    let consRHS ← mkLurkExpr consRHS.toImplicitLambda
    let cases := ⟦
      (if $(argName)
          (let ((head (car $(argName)))
                (tail (cdr $(argName))))
            $(consRHS))
          $(nilRHS))
    ⟧
    return (recrName.toString false, ⟦(lambda ($recrArgs) $cases)⟧)

  partial def mkRecursor (recrType : Expr) (recrName : Name) (recrIndices : Nat) (rhs : List Constructor) :
      TranspileM (String × AST) := do
    let ctorName := rhs.head?.map Constructor.name
    if ctorName = some ``List.nil || ctorName = some ``List.cons then
      mkListRecursor recrType recrName rhs
    else
      let (_, bindings) := telescope recrType
      let (argName, _) : Name × Expr := bindings.last!
      let recrArgs : List Name ← bindings.mapM fun (n, _) => replaceName n
      let ifThens ← rhs.mapM fun ctor => do
        let (idx, fields, rhs) := (ctor.idx, ctor.fields, ctor.rhs)

        let (rhs, binds) := telescope rhs

        let rhs ← mkLurkExpr rhs
        let _lurk_ctor_args := ⟦(getelem (cdr (cdr $argName)) 2)⟧
        let ctorArgs := (List.range fields).map fun (n : Nat) => ⟦(getelem _lurk_ctor_args $n)⟧

        let rhsCtorArgNames := binds.map Prod.fst |>.takeLast (fields - recrIndices)

        let bindings := (`_lurk_ctor_args, _lurk_ctor_args) :: rhsCtorArgNames.zip ctorArgs
        return (⟦(= (car (cdr $argName)) $idx)⟧, ⟦(let $bindings $rhs)⟧) -- extract snd element

      let cases := AST.mkIfElses ifThens ⟦nil⟧
      return (recrName.toString false, ⟦(lambda ($recrArgs) $cases)⟧)

  partial def mkInductiveBlock (inds : List (Inductive × List Constructor × IntRecursor × List ExtRecursor)) :
      TranspileM Unit := do
    for (ind, ctors, irecr, erecrs) in inds do
      if (← get).visited.contains ind.name then
        break
      appendBinding (ind.name, ← mkIndLiteral ind)
      for ctor in ctors do
        mkConstructor ctor ⟦,($(toString ind.name) $(ind.params) $(ind.indices))⟧ ind.indices
      let erecrs ← erecrs.mapM fun erecr =>
        mkRecursor erecr.type erecr.name erecr.indices $ erecr.rules.map (·.ctor)
      let irecr ← mkRecursor irecr.type irecr.name irecr.indices ctors
      match mkMutualBlock (irecr::erecrs) with
        | .ok xs => xs.forM fun (n, e) => appendBinding (n, e) false
        | .error e => throw $ .custom e

  -- partial def mkStructure

  -- partial def indInfoToLurkExpr (inds : List (Inductive × List Constructor × IntRecursor × List ExtRecursor)) :
  --     TranspileM Unit := do match inds with
  --   | [(ind, ctors, irecr, erecr)] =>
  --     match ind.struct, erecr with
  --     | some ctor, [] => _
  --     | _, _ => _
  --   | inds => mutIndBlockToLurkExpr inds

  partial def builtinInitialize (name : Name) (func : AST) : TranspileM Unit := do
    visit name
    go func
    appendBinding (name, func) (vst := false)
  where
    go : AST → TranspileM Unit
      | .sym n => do
        if !(← get).visited.contains n then
          match (← read).map.find? n with
          | some const => mkConst const
          | none => return
            -- TODO: better detection of what to compile, use this carefully for now
            -- throw $ .custom s!"built constant contains unknown symbol {name}"
      | .num _ | .char _ | .str _ => return
      | .cons e₁ e₂ => do go e₁; go e₂

  partial def mkLurkExpr (e : Expr) : TranspileM AST := do
    -- dbg_trace ">> mkLurkExpr: "
    match e with
    | .sort  .. => return ⟦nil⟧
    | .var name _ =>
      -- dbg_trace s!"var {name}"
      mkName name
    | .const name idx .. => do
      -- dbg_trace s!"const {name} {idx}"
      if !(← get).visited.contains name then
        match (← read).builtins.find? (fun (n, _) => n == name) with
        | some (n, e) =>
          builtinInitialize n e
        | none =>
          let const := (← read).tcStore.consts[idx]! -- TODO: Add proof later
          mkConst const
      mkName name
    | .app fn arg =>
      let e := ~[(← mkLurkExpr fn), (← mkLurkExpr arg)]
      -- TODO: this may be super efficient, need to analyze
      match Simp.getOfNatLit e with
      | some n => return .num n
      | none => return e
    | e@(.lam ..) =>
      -- dbg_trace s!"lam"
      mkLambda e
    | .pi    .. => return ⟦nil⟧
    | .letE name _ value body  => do
      -- dbg_trace s!"let {name}"
      let val ← mkLurkExpr value
      let body ← mkLurkExpr body
      return ⟦(let $([(name, val)]) $body)⟧
    | .lit lit  => match lit with
      -- TODO: need to include `Int` somehow
      | .natVal n =>
        -- dbg_trace s!"lit {n}";
        return ⟦$n⟧
      | .strVal s =>
        -- dbg_trace s!"lit {s}";
        return ⟦$s⟧
    | .proj idx e => do
      -- dbg_trace s!"proj {idx}";
      -- this is very nifty; `e` contains its type information *at run time*
      -- which we can take advantage of to compute the projection
      let e ← mkLurkExpr e
      let args := ⟦(getelem (cdr (cdr $e)) 2)⟧
      return ⟦(getelem $args $idx)⟧

  /--
  We're trying to compile the mutual blocks at once instead of compiling each
  projection separately to avoid some recursions.
  Arthur: I think there are some complications with mutual blocks for inductives
  because of recursors and constructors. We need to make sure we won't translate
  the same block more than once.
  -/
  partial def mkConst (c : Const) : TranspileM Unit := do
    -- dbg_trace s!">> mkConst {c.name}"
    match c with
    | .axiom    _
    | .quotient _ => return
    | .theorem  x =>
      if !(← get).visited.contains x.name then
        let (_, binds) := telescope x.type
        let binds : List Name ← binds.mapM fun (n, _) => replaceName n
        appendBinding (← replaceName x.name, ⟦(lambda ($binds) t)⟧)
    | .opaque x =>
      if !(← get).visited.contains x.name then
        visit x.name -- force cache update before `mkLurkExpr` to prevent looping
        appendBinding (← replaceName x.name, ← mkLurkExpr x.value) false
    | .definition x =>
      if !(← get).visited.contains x.name then
        match ← getMutualDefInfo x with
        | [ ] => throw $ .custom "empty `all` dereference; broken implementation"
        | [d] =>
          visit d.name -- force cache update before `mkLurkExpr` to prevent looping
          appendBinding (← replaceName d.name, ← mkLurkExpr d.value) false
        | defs =>
          defs.forM fun d => visit d.name
          let pairs ← defs.mapM fun d => return (d.name.toString false, ← mkLurkExpr d.value)
          match mkMutualBlock pairs with
          | .ok block => block.forM fun (n, e) => do appendBinding (← replaceName n, e) false
          | .error err => throw $ .custom err
    | .inductive x =>
      let u ← getMutualIndInfo x
      mkInductiveBlock u
    | .constructor x
    | .extRecursor x
    | .intRecursor x => processInductive x.name
  where
    getInductive (name : Name) : TranspileM Inductive := do
      let indName := name.getPrefix
      match (← read).map.find? indName with
      | some (.inductive i) => return i
      | some x => throw $ .invalidConstantKind x.name "inductive" x.ctorName
      | none => dbg_trace name; throw $ .notFoundInMap indName
    processInductive (name : Name) : TranspileM Unit := do
      let i ← getInductive name
      let u ← getMutualIndInfo i
      mkInductiveBlock u

end

/-- Initialize builtin lurk constants defined in `LurkFunctions.lean` -/
def builtins : List (Name × AST) := [
  Lurk.Functions.Nat,
  Lurk.Functions.NatZero,
  Lurk.Functions.NatSucc,
  Lurk.Functions.NatRec,
  Lurk.Functions.NatAdd,
  Lurk.Functions.NatMul,
  Lurk.Functions.NatDiv,
  Lurk.Functions.NatDecLe,
  Lurk.Functions.Char,
  Lurk.Functions.CharMk,
  Lurk.Functions.CharVal,
  Lurk.Functions.CharValid,
  Lurk.Functions.CharRec,
  Lurk.Functions.List,
  Lurk.Functions.ListNil,
  Lurk.Functions.ListCons,
  Lurk.Functions.ListRec,
  -- Lurk.Functions.ListMap,
  -- Lurk.Functions.ListFoldl,
  Lurk.Functions.String,
  Lurk.Functions.StringMk,
  Lurk.Functions.StringData,
  Lurk.Functions.StringRec
]

open Yatima.Transpiler

def initializePrimitives : TranspileM Unit := do
  let decls := [
    Lurk.Functions.getelem,
    Lurk.Functions.lurk_string_mk,
    Lurk.Functions.lurk_string_data
  ]
  for (n, e) in decls do
    appendBinding (n, e)

/-- Main translation function -/
def transpileM (root : Name) : TranspileM Unit := do
  initializePrimitives
  match (← read).tcStore.consts.find? fun c => c.name == root with
  | some c => mkConst c
  | none => throw $ .custom s!"Unknown const {root}"

/--
Constructs a `AST.letRecE` whose body is the call to a `root` constant in
a context and whose bindings are the constants in the context (including `root`)
that are needed to define `root`.
-/
def transpile (store : IR.Store) (root : Name := `root) :
    Except String AST :=
  match Converter.extractPureStore store with
  | .error err => .error err
  | .ok pStore =>
    let map := pStore.consts.foldl (init := default)
      fun acc const => acc.insert const.name const
    let env := ⟨store, pStore, map, builtins⟩
    let state : TranspileState := ⟨#[], .empty, ⟨`x, 1⟩, .empty⟩
    match TranspileM.run env state (transpileM root) with
    | .ok    s => .ok $ ⟦(letrec $s.appendedBindings.data $root)⟧
    | .error e => .error e
