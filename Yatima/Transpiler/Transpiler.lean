import Yatima.Datatypes.Store
import Yatima.Transpiler.TranspileM
import Yatima.Transpiler.Utils
import Yatima.Transpiler.LurkFunctions 

namespace Yatima.Transpiler

open Yatima.FromIpld
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

  /-- This is a hack. TODO(Winston) explain why -/
  partial def mkProjections (ctor : Constructor) : TranspileM Unit := do 
    let (name, params, type) := (ctor.name, ctor.params, ctor.type)
    let (_, ⟨binds⟩) := descend type #[]
    for (i, bind) in (binds.drop params).enum do 
      let projName := name.getPrefix ++ bind
      let args := (List.range params).map fun i => Lean.Name.mkSimple s!"_{i}"
      appendBinding (projName, ⟦(
        lambda ($args self) (getelem (cdr (cdr self)) $(params + i))
      )⟧)
  where
    descend (expr : Expr) (bindAcc : Array Name) : Expr × Array Name :=
      match expr with 
        | .pi name _ _ body => descend body <| bindAcc.push name
        | _ => (expr, bindAcc)

  partial def ctorToLurkExpr (ctor : Constructor) : TranspileM Unit := do 
      -- For example, the type of `Nat.succ` is `Nat → Nat`,
      -- but we don't want to translate the type; 
      -- we want to build a lambda out of this type
      -- which requires (a bit awkwardly) descending into
      -- the foralls and reconstructing a `lambda` term
    let (name, idx, type) := (ctor.name, ctor.idx, ctor.type)
    let (_, ⟨binds⟩) := descend type #[]
    let lurkBinds := binds.foldr (
      fun (n : Name) (acc : Lurk.Expr) => ⟦(cons $n $acc)⟧
    ) ⟦nil⟧
    let body := if binds.length == 0 then 
      ⟦(cons $(name.getPrefix) $idx)⟧
    else ⟦
      (lambda ($binds) (
        cons $(name.getPrefix) (cons $idx $lurkBinds)
      ))
    ⟧
    appendBinding (name, body)
  where 
    descend (expr : Expr) (bindAcc : Array Name) : Expr × Array Name :=
      match expr with 
        | .pi name _ _ body => descend body <| bindAcc.push name
        | _ => (expr, bindAcc)

  -- Very delicate, requires logic on the 
  -- indices/major/minor arguments of the inductive
  -- in order to insert the argument correctly.
  -- See lines 27 and 38 in `TypeChecker.Eval`
  -- partial def ruleRHSToLurkExpr (rhs : Expr) : Lurk.Expr := sorry

  -- partial def extRecrToLurkExpr (recr : ExtRecursor) (ind : Inductive) : TranspileM Unit := sorry

  partial def intRecrToLurkExpr (recr : IntRecursor) (rhs : List Constructor) : TranspileM Unit := do 
    let (_, ⟨binds⟩) := descend recr.type #[]
    let argName : Lurk.Expr := .lit $ .sym binds.last!
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
  where
    descend (expr : Expr) (bindAcc : Array Name) : Expr × Array Name :=
      match expr with 
        | .pi name _ _ body => descend body <| bindAcc.push name
        | _ => (expr, bindAcc)

  partial def mutIndBlockToLurkExpr (inds : List (Inductive × List Constructor × IntRecursor × List ExtRecursor)) : 
      TranspileM Unit := do
    for (ind, ctors, irecr, _) in inds do
      if (← get).visited.contains ind.name then 
        break
      appendBinding (ind.name, ⟦,($(toString ind.name) $(ind.params) $(ind.indices))⟧)
      intRecrToLurkExpr irecr ctors
      ctors.forM ctorToLurkExpr
      -- match ind.struct with 
      -- | some ctor => 
      --   ctorToLurkExpr ctor 
      --   mkProjections ctor
      -- | none => ctors.forM ctorToLurkExpr

  partial def exprToLurkExpr : Expr → TranspileM Lurk.Expr
    | .sort  ..
    | .lty   .. => return ⟦nil⟧
    | .var name _     => return ⟦$name⟧
    | .const name cid .. => do
      let visited? := (← get).visited.contains name
      if !visited? then 
        let const := (← read).defns[cid]! -- TODO: Add proof later
        -- The binding works here because `constToLurkExpr`
        -- will recursively process its children.
        -- Hence we know that this binding will always come after
        -- all of its children have already been bound 
        constToLurkExpr const
      return ⟦$name⟧
    | e@(.app ..) => telescopeApp e
    | e@(.lam ..) => telescopeLam e
    -- TODO: Do we erase?
    -- MP: I think we erase
    | .pi    .. => return ⟦nil⟧
    | .letE name _ value body  => do
      let val ← exprToLurkExpr value 
      let body ← exprToLurkExpr body
      return .letE [(name, val)] body
    | .lit lit  => match lit with 
      -- TODO: need to include `Int` somehow
      | .nat n => return ⟦$n⟧
      | .str s => return ⟦$s⟧
    | .proj idx e => do
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
  -- appendBinding Lurk.append
  -- appendBinding Lurk.length
  -- appendBinding Lurk.take
  -- appendBinding Lurk.drop
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
