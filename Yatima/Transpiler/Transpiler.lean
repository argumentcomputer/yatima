import Yatima.Datatypes.Store
import Yatima.Transpiler.TranspileM
import Yatima.Transpiler.Utils
import Yatima.Transpiler.LurkFunctions 

/-!
# The Transpiler

This file provides all core functions needed to build Lurk expressions from raw Yatima IR. 

Each function takes some Yatima object and converts it to its lurk representation; 
we follow the naming convention `<yatima-object>ToLurkExpr`.

For many functions, we choose to return `TranspileM Unit` instead of `TranspileM Lurk.Expr`. 
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
-/

namespace Yatima.Transpiler

open Yatima.Converter

mutual
    
  /-- Converts Yatima lambda `fun x₁ x₂ .. => body` into `Lurk.Expr.lam [x₁, x₂, ..] body` -/    
  partial def telescopeLam (expr : Expr) : TranspileM Lurk.Expr := 
    let rec descend (expr : Expr) (bindAcc : List Name) : Expr × List Name :=
      match expr with 
        | .lam _ name _ _ body => descend body <| bindAcc.concat name
        | _ => (expr, bindAcc)
    do
      let (expr, binds) := descend expr []
      let fn ← exprToLurkExpr expr
      return .lam binds fn

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
  partial def ctorToLurkExpr (ctor : Constructor) (indices : Nat) : TranspileM Unit := do 
    let (name, idx, params, type) := (ctor.name, ctor.idx, ctor.params, ctor.type)
    let (_, ⟨binds⟩) := descendPi type #[]
    let lurkBinds := binds.foldr (
      fun (n : Name) (acc : Lurk.Expr) => ⟦(cons $n $acc)⟧
    ) ⟦nil⟧
    -- if the inductive has arguments, then apply them from `ctor`'s bindings
    let ind : Lurk.Expr := match (indices + params) with 
      | 0 => ⟦$(name.getPrefix)⟧
      | _ => .mkApp ⟦$(name.getPrefix)⟧ $ binds.take (params + indices) |>.map fun (n : Name) => ⟦$n⟧
    let body := if binds.length == 0 then 
      ⟦(cons $ind (cons $idx nil))⟧
    else ⟦
      (lambda ($binds) (
        cons $ind (cons $idx $lurkBinds)
      ))
    ⟧
    appendBinding (name, body)

  partial def recrToLurkExpr (recrType : Expr) (recrName : Name) (recrIndices : Nat) (rhs : List Constructor) : TranspileM Unit := do
    let (_, ⟨binds⟩) := descendPi recrType #[]
    let argName : Lurk.Expr := ⟦$(binds.last!)⟧
    let ifThens ← rhs.mapM fun ctor => do 
      let (idx, fields, rhs) := (ctor.idx, ctor.fields, ctor.rhs)
      let rhs ← exprToLurkExpr rhs 
      let args := ⟦(cdr (cdr $argName))⟧
      let ctorArgs := (List.range fields).map fun (n : Nat) => ⟦(getelem $args (+ $n (getelem (car $argName) 1)))⟧
      let recrArgs := binds.reverse.drop (recrIndices + 1) |>.map fun (n : Name) => ⟦$n⟧
      let newArgs := recrArgs.reverse ++ ctorArgs
      return (⟦(= (car (cdr $argName)) $idx)⟧, .mkApp rhs newArgs) -- extract snd element
    let cases := Lurk.Expr.mkIfElses ifThens ⟦nil⟧
    appendBinding (recrName, ⟦(lambda ($binds) $cases)⟧)

  partial def mutIndBlockToLurkExpr (inds : List (Inductive × List Constructor × IntRecursor × List ExtRecursor)) : 
      TranspileM Unit := do
    for (ind, ctors, irecr, erecrs) in inds do
      if (← get).visited.contains ind.name then 
        break
      let (_, ⟨binds⟩) := descendPi ind.type #[]
      -- when the inductive type is a function, i.e.
      -- we have params or indices, then `lurkInd` is 
      -- encoded as a lambda
      let lurkInd := if binds.isEmpty then
        -- TODO: fix back to use `quote`
        ⟦(cons $(toString ind.name) (cons $(ind.params) (cons $(ind.indices) nil)))⟧
      else 
        ⟦(lambda ($binds) 
            (cons $(toString ind.name) (cons $(ind.params) (cons $(ind.indices) nil))))⟧
      appendBinding (ind.name, lurkInd)
      for erecr in erecrs do
        recrToLurkExpr erecr.type erecr.name erecr.indices $ erecr.rules.map (·.ctor)
      recrToLurkExpr irecr.type irecr.name irecr.indices ctors
      ctors.forM fun c => ctorToLurkExpr c ind.indices

  partial def exprToLurkExpr (e : Expr) : TranspileM Lurk.Expr := do  
    -- IO.print ">> exprToLurkExpr: "
    match e with 
    | .sort  ..
    | .lty   .. => return ⟦nil⟧
    | .var _ name _     => 
      -- IO.println s!"var {name}"
      return ⟦$name⟧
    | .const _ name idx .. => do
      -- IO.println s!"const {name} {idx}"
      if !(← get).visited.contains name then 
        let const := (← read).compileState.consts[idx]! -- TODO: Add proof later
        constToLurkExpr const
      return ⟦$name⟧
    | .app _ fn arg => 
      -- IO.println s!"app"
      return .app (← exprToLurkExpr fn) (← exprToLurkExpr arg)
    | e@(.lam ..) => 
      -- IO.println s!"lam"
      telescopeLam e
    | .pi    .. => return ⟦nil⟧
    | .letE _ name _ value body  => do
      -- IO.println s!"let {name}"
      let val ← exprToLurkExpr value
      let body ← exprToLurkExpr body
      return .letE [(name, val)] body
    | .lit _ lit  => match lit with
      -- TODO: need to include `Int` somehow
      | .num n =>
        -- IO.println s!"lit {n}";
        return ⟦$n⟧
      | .word s =>
        -- IO.println s!"lit {s}";
        return ⟦$s⟧
    | .proj _ idx e => do
      -- IO.println s!"proj {idx}";
      -- this is very nifty; `e` contains its type information *at run time*
      -- which we can take advantage of to compute the projection
      let e ← exprToLurkExpr e
      -- TODO(Winston): inlining of `e` causes term size blowup, need to remove
      let offset := ⟦(+ (getelem (car $e) 1) (getelem (car $e) 2))⟧
      let args := ⟦(cdr (cdr $e))⟧
      return ⟦(getelem $args (+ $offset $idx))⟧

  /--
  We're trying to compile the mutual blocks at once instead of compiling each
  projection separately to avoid some recursions.
  Arthur: I think there are some complications with mutual blocks for inductives
  because of recursors and constructors. We need to make sure we won't translate
  the same block more than once.
  -/
  partial def constToLurkExpr (c : Const) : TranspileM Unit := do 
    -- IO.println s!">> constToLurkExpr {c.name}"
    match c with 
    | .axiom    _
    | .quotient _ => return
    | .theorem  x => 
      if !(← get).visited.contains x.name then 
        let (_, ⟨binds⟩) := descendPi x.type #[]
        appendBinding (x.name, ⟦(lambda ($binds) t)⟧)
    | .opaque x =>
      if !(← get).visited.contains x.name then
        visit x.name -- force cache update before `exprToLurkExpr` to prevent looping
        appendBindingNoVisit (x.name, ← exprToLurkExpr x.value)
    | .definition x =>
      if !(← get).visited.contains x.name then
        match ← getMutualDefInfo x with
        | [ ] => throw $ .custom "empty `all` dereference; broken implementation"
        | [d] =>
          visit d.name
          appendBindingNoVisit (d.name, ← exprToLurkExpr d.value)
        | defs =>
          defs.forM fun d => visit d.name
          let pairs ← defs.mapM fun d => return (d.name, ← exprToLurkExpr d.value)
          Lurk.Expr.mkMutualBlock pairs |>.forM
            fun (n, e) => appendBindingNoVisit (n, e)
    | .inductive x =>
      let u ← getMutualIndInfo x
      mutIndBlockToLurkExpr u
    | .constructor x
    | .extRecursor x
    | .intRecursor x => processInductive x.name
  where 
    getInductive (name : Name) : TranspileM Inductive := do 
      let indName := name.getPrefix
      let store := (← read).compileState
      match store.cache.find? indName with 
      | some (_, idx) => match store.consts[idx]! with 
        | .inductive i => return i 
        | x => throw $ .invalidConstantKind x "inductive"
      | none => throw $ .notFoundInCache indName
    processInductive (name : Name) : TranspileM Unit := do 
      let i ← getInductive name
      let u ← getMutualIndInfo i
      mutIndBlockToLurkExpr u

end

/-- Initialize builtin lurk constants defined in `LurkFunctions.lean` -/
def builtinInitialize : TranspileM Unit := do 
  let decls := [
    Lurk.getelem, 
    Lurk.Nat, 
    Lurk.Nat_zero, 
    Lurk.Nat_succ, 
    Lurk.Nat_rec,
    Lurk.Nat_add,
    Lurk.Nat_mul,
    Lurk.Nat_div,
    Lurk.Nat_decLe
  ] 
  withBuiltin (decls.map fun x => x.fst) $ 
    decls.forM fun (n, e) => appendBinding (n, e)

/-- Main translation function -/
def transpileM : TranspileM Unit := do
  let store := (← read).compileState
  builtinInitialize
  for c in store.consts do 
    if c.name == `root then 
      constToLurkExpr c

/-- Constructs the array of bindings and builds a `Lurk.Expr.letRecE` from it -/
def transpile (filePath : System.FilePath) (body : Lurk.Expr) : IO $ Except String Lurk.Expr := do
  match ← Compiler.compile filePath with
  | .ok ctx => return match ← TranspileM.run ⟨ctx, []⟩ default transpileM with
    | .ok    s => .ok $ Lurk.Expr.letRecE s.appendedBindings.data ⟦$body⟧
    | .error e => .error e
  | .error err => .error (toString err)

def transpile' (ctx : Context) (body : Lurk.Expr := ⟦(current-env)⟧): IO $ Except String Lurk.Expr := do
  return match ← TranspileM.run ctx default transpileM with
  | .ok    s => .ok $ Lurk.Expr.letRecE s.appendedBindings.data body
  | .error e => .error e

end Yatima.Transpiler
