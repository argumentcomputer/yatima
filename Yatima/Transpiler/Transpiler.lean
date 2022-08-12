import Yatima.Datatypes.Store
import Yatima.Transpiler.TranspileM
import Yatima.Transpiler.Utils
import Yatima.Transpiler.LurkFunctions 

namespace Yatima.Transpiler

open Yatima.Converter

mutual

  partial def telescopeApp (expr : Expr) : TranspileM Lurk.Expr := 
    let rec descend (expr : Expr) (argAcc : List Expr) : Expr × List Expr :=
      match expr with 
        | .app fn arg => descend fn <| arg :: argAcc
        | _ => (expr, argAcc)
    do
      let (expr, args) := descend expr []
      let fn ← exprToLurkExpr expr
      let args ← args.mapM exprToLurkExpr
      return .app fn args
        
  partial def telescopeLam (expr : Expr) : TranspileM Lurk.Expr := 
    let rec descend (expr : Expr) (bindAcc : List Name) : Expr × List Name :=
      match expr with 
        | .lam name _ _ body => descend body <| bindAcc.concat name
        | _ => (expr, bindAcc)
    do
      let (expr, binds) := descend expr []
      let fn ← exprToLurkExpr expr
      return .lam binds fn

  /-- TODO(Winston): Explain `indices` argument -/
  partial def ctorToLurkExpr (ctor : Constructor) (indices : Nat) : TranspileM Unit := do 
    let (name, idx, params, type) := (ctor.name, ctor.idx, ctor.params, ctor.type)
    let (_, ⟨binds⟩) := descendPi type #[]
    let lurkBinds := binds.foldr (
      fun (n : Name) (acc : Lurk.Expr) => ⟦(cons $n $acc)⟧
    ) ⟦nil⟧
    -- TODO(Winston): Explain
    let ind : Lurk.Expr := match (indices + params) with 
      | 0 => ⟦$(name.getPrefix)⟧
      | _ => .app ⟦$(name.getPrefix)⟧ $ binds.take (params + indices) |>.map fun (n : Name) => ⟦$n⟧
    let body := if binds.length == 0 then 
      ⟦(cons $ind (cons $idx nil))⟧
    else ⟦
      (lambda ($binds) (
        cons $ind (cons $idx $lurkBinds)
      ))
    ⟧
    appendBinding (name, body)

  -- TODO: Implement
  -- partial def extRecrToLurkExpr (recr : ExtRecursor) (ind : Inductive) : TranspileM Unit := sorry

  partial def intRecrToLurkExpr (recr : IntRecursor) (rhs : List Constructor) : TranspileM Unit := do 
    let (_, ⟨binds⟩) := descendPi recr.type #[]
    let argName : Lurk.Expr := ⟦$(binds.last!)⟧
    let ifThens ← rhs.mapM fun ctor => do 
      let (idx, fields, rhs) := (ctor.idx, ctor.fields, ctor.rhs)
      let rhs ← exprToLurkExpr rhs 
      let args := ⟦(cdr (cdr $argName))⟧
      let ctorArgs := (List.range fields).map fun (n : Nat) => ⟦(getelem $args $n)⟧
      let recrArgs := binds.reverse.drop (recr.indices + 1) |>.map fun (n : Name) => ⟦$n⟧
      let newArgs := recrArgs.reverse ++ ctorArgs
      return (⟦(= (car (cdr $argName)) $idx)⟧, .app rhs newArgs) -- extract snd element
    let cases := Lurk.Expr.mkIfElses ifThens ⟦nil⟧
    appendBinding (recr.name, ⟦(lambda ($binds) $cases)⟧)

  partial def mutIndBlockToLurkExpr (inds : List (Inductive × List Constructor × IntRecursor × List ExtRecursor)) : 
      TranspileM Unit := do
    for (ind, ctors, irecr, _) in inds do
      if (← get).visited.contains ind.name then 
        break
      let (_, ⟨binds⟩) := descendPi ind.type #[]
      -- TODO(Winston): Explain
      let lurkInd := if binds.length == 0 then 
        ⟦,($(toString ind.name) $(ind.params) $(ind.indices))⟧
      else 
        ⟦(lambda ($binds) ,($(toString ind.name) $(ind.params) $(ind.indices)))⟧
      appendBinding (ind.name, lurkInd)
      intRecrToLurkExpr irecr ctors
      ctors.forM fun c => ctorToLurkExpr c ind.indices

  partial def exprToLurkExpr (e : Expr) : TranspileM Lurk.Expr := do  
    IO.print ">> exprToLurkExpr: "
    match e with 
    | .sort  ..
    | .lty   .. => return ⟦nil⟧
    | .var name _     => 
      IO.println s!"var {name}"
      return ⟦$name⟧
    | .const name idx .. => do
      IO.println s!"const {name} {idx}"
      let visited? := (← get).visited.contains name
      if !visited? then 
        let const := (← read).defns[idx]! -- TODO: Add proof later
        constToLurkExpr const
      return ⟦$name⟧
    | e@(.app ..) => 
      IO.println s!"app"
      telescopeApp e
    | e@(.lam ..) => 
      IO.println s!"lam"
      telescopeLam e
    | .pi    .. => return ⟦nil⟧
    | .letE name _ value body  => do
      IO.println s!"let {name}"
      let val ← exprToLurkExpr value 
      let body ← exprToLurkExpr body
      return .letE [(name, val)] body
    | .lit lit  => match lit with 
      -- TODO: need to include `Int` somehow
      | .nat n => IO.println s!"lit {n}"; return ⟦$n⟧
      | .str s => IO.println s!"lit {s}"; return ⟦$s⟧
    | .proj idx e => do
      IO.println s!"proj {idx}"; 
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
    IO.println s!">> constToLurkExpr {c.name}"
    match c with 
    | .axiom    _
    | .quotient _ => return ()
    | .theorem  x => 
      if (← get).visited.contains x.name then return 
      else appendBinding (x.name, .lit .t)
    | .opaque   x => do 
      if (← get).visited.contains x.name then 
        return 
      else 
        visit x.name -- force cache update before `exprToLurkExpr` to prevent looping
        appendBindingNoVisit (x.name, ← exprToLurkExpr x.value)
    | .definition x => do
      if (← get).visited.contains x.name then 
        return 
      else 
        visit x.name -- ditto
        appendBindingNoVisit (x.name, ← exprToLurkExpr x.value)
    | .inductive x => do 
      let u ← getMutualIndInfo x
      mutIndBlockToLurkExpr u
    | .constructor x
    | .extRecursor x
    | .intRecursor x => processInductive x.name
  where 
    getInductive (name : Name) : TranspileM Inductive := do 
      let indName := name.getPrefix
      let store ← read
      match store.cache.find? indName with 
      | some (_, idx) => match store.defns[idx]! with 
        | .inductive i => return i 
        | x => throw $ .invalidConstantKind x "inductive"
      | none => throw $ .notFoundInCache indName
    processInductive (name : Name) : TranspileM Unit := do 
      let i ← getInductive name
      let u ← getMutualIndInfo i
      mutIndBlockToLurkExpr u

end

/-- 
Initialize builtin lurk constants defined in `LurkFunctions.lean`
-/
def builtinInitialize : TranspileM Unit := do
  appendBinding Lurk.getelem

/--
Main translation function.
-/
def transpileM : TranspileM Unit := do
  let store ← read
  builtinInitialize
  store.defns.forM constToLurkExpr

open Yatima.Compiler in 
/-- Constructs the array of bindings and builds a `Lurk.Expr.letRecE` from it. -/
def transpile (store : CompileState) : IO $ Except String String := do  do 
  match ← TranspileM.run store default transpileM with
  | .ok    s => 
    let env := Lurk.Expr.letRecE s.appendedBindings.data ⟦(current-env)⟧ -- the parens matter, represents evaluation
    return .ok $ (env.pprint false).pretty 50
  | .error e => 
    return .error e

end Yatima.Transpiler