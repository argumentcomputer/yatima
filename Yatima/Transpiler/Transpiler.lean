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
        | .app fn arg => descend fn <| argAcc.concat arg
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

  partial def ctorToLurkExpr (ctor : Constructor) : TranspileM Unit := do 
      -- For example, the type of `Nat.succ` is `Nat → Nat`,
      -- but we don't want to translate the type; 
      -- we want to build a lambda out of this type
      -- which requires (a bit awkwardly) descending into
      -- the foralls and reconstructing a `lambda` term
    let (name, idx, type) := (ctor.name, ctor.idx, ctor.type)
    let (_, ⟨binds⟩) := descend type #[]
    let lurkBinds := binds.foldl (
      fun (acc : Lurk.Expr) (n : Name) => ⟦(cons $n $acc)⟧
    ) ⟦nil⟧
    let body := if binds.length == 0 then 
      ⟦,($(toString name) $idx)⟧
    else ⟦
      (lambda ($binds) (
        append ,($(toString name) $idx) $lurkBinds
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

  partial def exprToLurkExpr : Expr → TranspileM Lurk.Expr
    | .sort  ..
    | .lty   .. => return ⟦nil⟧
    | .var name _     => return ⟦$name⟧
    | .const name cid .. => do
      let visited? := (← get).visited.contains name
      if !visited? then 
        visit name -- cache
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
    -- TODO
    | .letE name _ value body  => do
      let val ← exprToLurkExpr value 
      let body ← exprToLurkExpr body
      return .letE [(name, val)] body
    | .lit lit  => match lit with 
      -- TODO: need to include `Int` somehow
      | .nat n => return ⟦$n⟧
      | .str s => return ⟦$s⟧
    -- TODO
    -- MP: .proj should also go to .nil right? I am probably wrong though.
    | .proj  .. => return ⟦nil⟧

  -- /--
  --  FIX: This is wrong, it just returns the literal name for unit type constructors, but it does 
  --       help with debugging some of the above functions
  -- -/
  partial def mutIndBlockToLurkExpr (inds : List (Name × List Name × Name × List Name)) : 
      TranspileM Unit := do
    let store ← read
    for (ind, ctors, intR, _) in inds do
      if (← get).visited.contains ind then 
        break
      visit ind
      appendBinding (ind, ⟦nil⟧)
      let ctors ← ctors.mapM fun ctor => 
        match store.cache.find? ctor with 
        | some (_, idx) => match store.defns[idx]! with 
          | .constructor ctor => return ctor 
          | x => throw $ .invalidConstantKind x "constructor"
        | none => throw $ .notFoundInCache ctor
      let irecr : IntRecursor := ← match store.cache.find? intR with 
        | some (_, idx) => match store.defns[idx]! with 
          | .intRecursor recr => return recr 
          | x => throw $ .invalidConstantKind x "internal recursor"
        | none => throw $ .notFoundInCache intR
      for ctor in ctors do
        visit ctor.name
        ctorToLurkExpr ctor
      visit irecr.name
      intRecrToLurkExpr irecr ctors

  /--
  We're trying to compile the mutual blocks at once instead of compiling each
  projection separately to avoid some recursions.

  Arthur: I think there are some complications with mutual blocks for inductives
  because of recursors and constructors. We need to make sure we won't translate
  the same block more than once.
  -/
  partial def constToLurkExpr : Const → TranspileM Unit
    | .axiom    _
    | .quotient _ => return ()
    | .theorem  x => appendBinding (x.name, .lit .t)
    | .opaque   x => do appendBinding (x.name, ← exprToLurkExpr x.value)
    | .definition x => do appendBinding (x.name, ← exprToLurkExpr x.value)
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
  appendBinding Lurk.append
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
def transpile (store : CompileState) : IO $ Except String String := do 
  match ← TranspileM.run store default transpileM with
  | .ok    s => 
    let env := Lurk.Expr.letRecE s.appendedBindings.data ⟦(current-env)⟧ -- the parens matter, represents evaluation
    return .ok $ (env.pprint false).pretty 50
  | .error e => 
    return .error e

end Yatima.Transpiler
