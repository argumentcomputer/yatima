import Yatima.Datatypes.Store
import Yatima.Transpiler.TranspileM
import Yatima.Transpiler.Utils

namespace Yatima.Transpiler

open Yatima.FromIpld
mutual

  partial def telescopeApp (expr : Expr) : TranspileM $ Option Lurk.Expr := 
    let rec descend (expr : Expr) (argAcc : List Expr) : Expr × List Expr :=
      match expr with 
        | .app fn arg => descend fn <| argAcc.concat arg
        | _ => (expr, argAcc)
    do
      let (expr, args) := descend expr []
      let fn? ← exprToLurkExpr expr
      let args? : Option $ List Lurk.Expr := (← args.mapM exprToLurkExpr).foldl
        (fun acc? arg? => match acc?, arg? with
          | some acc, some arg => some $ acc.concat arg
          | _, _ => none) (some [])
      match fn?, args? with
      | some fn, some args => return some $ .app fn args
      | _, _ => return none
        
  partial def telescopeLam (expr : Expr) : TranspileM $ Option Lurk.Expr := 
    let rec descend (expr : Expr) (bindAcc : List Name) : Expr × List Name :=
      match expr with 
        | .lam name _ _ body => descend body <| bindAcc.concat name
        | _ => (expr, bindAcc)
    do
      let (expr, binds) := descend expr []
      let fn? ← exprToLurkExpr expr
      match fn? with
        | some fn => return some $ .lam (binds.map fixName) fn
        | none => return none

  partial def ctorToLurkExpr (ctor : Constructor) : TranspileM Unit := do 
      -- For example, the type of `Nat.succ` is `Nat → Nat`,
      -- but we don't want to translate the type; 
      -- we want to build a lambda out of this type
      -- which requires (a bit awkwardly) descending into
      -- the foralls and reconstructing a `lambda` term
    let (_, ⟨binds⟩) := descend ctor.type #[]
    let name := fixName ctor.name -- we need the string name too
    let binds := binds.map fixName
    appendBinding (ctor.name, ⟦(lambda ($binds) ,($name . $ctor.idx . $binds))⟧)
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
    let argName : Lurk.Expr := .lit $ .sym (fixName binds.last!)
    let ifThens ← rhs.mapM fun ctor => do 
      let (idx, fields, rhs) := (ctor.idx, ctor.fields, ctor.rhs)
      match ← exprToLurkExpr rhs with 
      | some rhs => 
        let args := ⟦(cdr (cdr $argName))⟧
        -- (List.drop (recur.indices + 1) binds) ++ (List.take ctor.fields args)
        return (⟦(= (cdr (car $argName)) $idx)⟧, ⟦($rhs)⟧) -- extract snd element
      | none => throw "failed to convert rhs of rule {idx}"
    let binds := binds.map fixName
    let cases := Lurk.Expr.mkIfElses ifThens ⟦nil⟧
    appendBinding (recr.name, ⟦(lambda ($binds) $cases)⟧) 
  where
    descend (expr : Expr) (bindAcc : Array Name) : Expr × Array Name :=
      match expr with 
        | .pi name _ _ body => descend body <| bindAcc.push name
        | _ => (expr, bindAcc)

  partial def exprToLurkExpr : Expr → TranspileM (Option Lurk.Expr)
    | .sort  ..
    | .lty   .. => return none
    | .var name _     => return some $ .lit $ .sym (fixName name)
    | .const name cid .. => do
      let visited? := (← get).visited.contains name
      if !visited? then 
        dbg_trace s!"visit {name}"
        visit name -- cache
        let const := (← read).defns[cid]! -- TODO: Add proof later
        -- The binding works here because `constToLurkExpr`
        -- will recursively process its children.
        -- Hence we know that this binding will always come after
        -- all of its children have already been bound 
        match ← constToLurkExpr const with 
          | some expr => appendBinding (name, expr)
          | none      => pure ()
      return some $ .lit $ .sym (fixName name)
    | e@(.app ..) => telescopeApp e
    | e@(.lam ..) => telescopeLam e
    -- TODO: Do we erase?
    -- MP: I think we erase
    | .pi    .. => return some ⟦nil⟧
    -- TODO
    | .letE name _ value body  => do
      match (← exprToLurkExpr value), (← exprToLurkExpr body) with
        | some val, some body => return some $ .letE [(fixName name, val)] body
        | _, _ => throw "TODO"
    | .lit lit  => match lit with 
      -- TODO: need to include `Int` somehow
      | .nat n => return some ⟦$n⟧
      | .str s => return some ⟦$s⟧
    -- TODO
    -- MP: .proj should also go to .nil right? I am probably wrong though.
    | .proj  .. => return some ⟦nil⟧

  -- /--
  --  FIX: This is wrong, it just returns the literal name for unit type constructors, but it does 
  --       help with debugging some of the above functions
  -- -/
  partial def mutIndBlockToLurkExpr (inds : List (Name × List Name × Name × List Name)) : 
      TranspileM Unit := do
    let store ← read
    for (ind, ctors, intR, extRs) in inds do
      dbg_trace s!"beep boop: {ind} being processed"
      let ctors ← ctors.mapM fun ctor => 
        match store.cache.find? ctor with 
        | some (_, idx) => match store.defns[idx]! with 
          | .constructor ctor => return ctor 
          | _ => throw s!"{ctor} not a constructor"
        | none => throw s!"{ctor} not found in cache"
      let irecr : IntRecursor := ← match store.cache.find? intR with 
        | some (_, idx) => match store.defns[idx]! with 
          | .intRecursor recr => return recr 
          | _ => throw s!"{intR} not a internal recursor"
        | none => throw s!"{intR} not found in cache"
      for ctor in ctors do
        ctorToLurkExpr ctor
      dbg_trace s!"ctors are good"
      intRecrToLurkExpr irecr ctors
      dbg_trace s!"irecr is good"
      
      -- for recr in extRs do 
      --   match store.cache.find? recr with 
      --   | some (_, idx) => match store.defns[idx]! with 
      --     | .intRecursor recr => intRecrToLurkExpr recr 
      --     | _ => throw ""
      --   | none => throw ""

    -- Winston: Idk how the implementation for mutuals
    -- makes everything interact, so for now I just 
    -- commented this out to focus on 1 inductive
    -- @Matej
    
    -- let ctorExprs := inds |>.map Inductive.ctors 
    --                       |>.join
    --                       |>.map (fun ctor => (ctor.name, ctor.rhs))

    -- for (exprName, exprCid) in ctorExprs do
    --   let mut ctorLurkExprs : List (String × Lurk.Expr) := [] 
    --   match store.expr_cache.find? exprCid with
    --     | none => throw "TODO"
    --     | some expr => 
    --       let lurkExpr? ← exprToLurkExpr expr
    --       match lurkExpr? with
    --         | none => throw "TODO"
    --         | some lExpr => 
    --           ctorLurkExprs := ctorLurkExprs.concat (fixName exprName, lExpr)
    -- return none

  /--
  We're trying to compile the mutual blocks at once instead of compiling each
  projection separately to avoid some recursions.

  Arthur: I think there are some complications with mutual blocks for inductives
  because of recursors and constructors. We need to make sure we won't translate
  the same block more than once.
  -/
  partial def constToLurkExpr : Const → TranspileM (Option Lurk.Expr)
    | .axiom         _
    | .quotient        _ => return none
    | .theorem  _ => return some (.lit .t)
    | .opaque   x => exprToLurkExpr x.value
    | .definition x => exprToLurkExpr x.value
    | .inductive x => do 
      let u ← getMutualIndInfo x
      dbg_trace u
      mutIndBlockToLurkExpr u
      return none -- I think since we're making the constructors and recursors constants now, we can nil this out?
    | .constructor x => return none
    | .extRecursor x => return none
    | .intRecursor x => return none
    -- TODO

end

/--
Main translation function.

FIX: we need to iterate on leaves of the `const_cache`, only!
FIX: we need to cache what's already been done for efficiency and correctness!
-/
def transpileM : TranspileM Unit := do
  let store ← read
  store.defns.forM fun const => do
    dbg_trace s!"processing {const.name}"
    match ← constToLurkExpr const with
    | some expr => appendBinding (const.name, expr)
    | none      => pure ()

open Yatima.Compiler in 
/-- Constructs the array of bindings and builds a `Lurk.Expr.letE` from it. -/
def transpile (store : CompileState) : Except String String :=
  match TranspileM.run store default transpileM with
  | .ok    s => return Lurk.Expr.print $ .letE s.getStringBindings .currEnv
  | .error e => throw e

end Yatima.Transpiler
