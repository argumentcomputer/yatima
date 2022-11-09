import Yatima.Datatypes.Store
import Yatima.Compiler.CompileError
import Yatima.LurkData.ToLurkData
import Yatima.Compiler.Utils

namespace Yatima.Compiler

open Std (RBMap)
open Lurk.Hashing Lurk.Syntax AST

/--
The state for the `Yatima.Compiler.CompileM` monad.

* `irStore` contains the resulting objects encoded in IR
* `tcStore` contains the resulting objects for typechecking
* `cache` has compiled data of constants, accessed by name

The IPLD arrays are used for the later encoding of the IR store in IPLD
-/
structure CompileState where
  irStore : IR.Store
  tcStore : TC.Store
  cache   : RBMap Name (IR.BothConstScalar × TC.ConstIdx) compare
  -- objects represented in `Lurk.Syntax.AST`
  consts    : Array AST
  univAnon  : Array AST
  exprAnon  : Array AST
  constAnon : Array AST
  univMeta  : Array AST
  exprMeta  : Array AST
  constMeta : Array AST
  -- contains cached data to speed up the encoding of Lurk data
  encodeState : EncodeState
  deriving Inhabited

def CompileState.lurkStore (s : CompileState) : Lurk.Store :=
  ⟨s.consts,
    s.univAnon, s.exprAnon, s.constAnon,
    s.univMeta, s.exprMeta, s.constMeta⟩

/-- Creates a summary off of a `Yatima.Compiler.CompileState` as a `String` -/
def CompileState.summary (s : CompileState) : String :=
  let consts := ", ".intercalate $ s.tcStore.consts.toList.map
    fun c => s!"{c.name} : {c.ctorName}"
  "Compilation summary:\n" ++
  s!"-----------Constants-----------\n" ++
  s!"{consts}\n" ++
  s!"-------------Sizes-------------\n" ++
  s!"  univ_anon  size: {s.irStore.univAnon.size}\n" ++
  s!"  univ_meta  size: {s.irStore.univMeta.size}\n" ++
  s!"  expr_anon  size: {s.irStore.exprAnon.size}\n" ++
  s!"  expr_meta  size: {s.irStore.exprMeta.size}\n" ++
  s!"  const_anon size: {s.irStore.constAnon.size}\n" ++
  s!"  const_meta size: {s.irStore.constMeta.size}\n" ++
  s!"  cache      size: {s.cache.size}"

/--
The type of entries for the `recrCtx`. It contains:
1. The index of the constant in the mutual block
2. The index in the list of weakly equal mutual definitions (N/A inductives)
3. The constant index in array of constants
-/
abbrev RecrCtxEntry := (Nat × Option Nat × TC.ConstIdx)

/--
The read-only environment for the `Yatima.Compiler.CompileM` monad.

* `constMap` is the original set of constants provided by Lean
* `univCtx` is the current list of universes
* `bindCtx` is the current list of binders
* `recrCtx` is keeps the information for names that represent recursive calls
* `log` tells whether the user wants to log the compilation
-/
structure CompileEnv where
  constMap : Lean.ConstMap
  univCtx  : List Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Name RecrCtxEntry compare
  log      : Bool
  deriving Inhabited

/-- Instantiates a `Yatima.Compiler.CompileEnv` from a map of constants -/
def CompileEnv.init (map : Lean.ConstMap) (log : Bool) : CompileEnv :=
  ⟨map, [], [], .empty, log⟩

/--
The monad in which compilation takes place is a stack of `ReaderT`, `ExceptT`
and `StateT` on top of IO
-/
abbrev CompileM := ReaderT CompileEnv $
  ExceptT CompileError $ StateT CompileState IO

/-- Basic runner function for `Yatima.Compiler.CompileEnv` -/
def CompileM.run (env : CompileEnv) (ste : CompileState) (m : CompileM α) :
    IO $ Except CompileError CompileState := do
  match ← StateT.run (ReaderT.run m env) ste with
  | (.ok _,  ste) => return .ok ste
  | (.error e, _) => return .error e

/-- Computes with a new binder in the monad environment -/
def withBinder (name : Name) : CompileM α → CompileM α :=
  withReader $ fun e =>
    ⟨e.constMap, e.univCtx, name :: e.bindCtx, e.recrCtx, e.log⟩

/-- Computes with a given list of levels and reset binders and `recrCtx` -/
def withLevelsAndReset (levels : List Name) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, levels, [], .empty, e.log⟩

/-- Computes with a given `recrCtx` -/
def withRecrs (recrCtx : RBMap Name RecrCtxEntry compare) :
    CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, e.univCtx, e.bindCtx, recrCtx, e.log⟩

/-- Computes with a given list of levels-/
def withLevels (lvls : List Name) : CompileM α → CompileM α :=
  withReader $ fun e => ⟨e.constMap, lvls, e.bindCtx, e.recrCtx, e.log⟩

/-- Possibly gets a `Yatima.Compiler.RecrCtxEntry` from the `recrCtx` by name -/
def getFromRecrCtx (name : Name) : CompileM $ Option RecrCtxEntry :=
  return (← read).recrCtx.find? name

/-- Forcibly gets a `Yatima.Compiler.RecrCtxEntry` from the `recrCtx` by name -/
def getFromRecrCtx! (name : Name) : CompileM $ RecrCtxEntry := do
  match ← getFromRecrCtx name with
  | some entry => pure entry
  | none => throw $ .notFoundInRecrCtx name

/-- Auxiliary type to standardize additions of CIDs to the store -/
inductive StoreEntry : Type → Type
  | univ  : IR.Both IR.Univ  → StoreEntry IR.BothUnivScalar
  | expr  : IR.Both IR.Expr  → StoreEntry IR.BothExprScalar
  | const : IR.Both IR.Const → StoreEntry IR.BothConstScalar

/-- Adds CID data to the store, but also returns it for practical reasons -/
def addToStore : StoreEntry A → CompileM A
  | .univ obj => do
    let (astAnon, ptrAnon, encStt) := obj.anon.encode (← get).encodeState
    let (astMeta, ptrMeta, encStt) := obj.meta.encode encStt
    modifyGet fun stt => (⟨ptrAnon, ptrMeta⟩, { stt with
      irStore := { stt.irStore with
        univAnon := stt.irStore.univAnon.insert ptrAnon obj.anon,
        univMeta := stt.irStore.univMeta.insert ptrMeta obj.meta }
      univAnon := stt.univAnon.push $ ~[ToAST.toAST ptrAnon, astAnon]
      univMeta := stt.univMeta.push $ ~[ToAST.toAST ptrMeta, astMeta]
      encodeState := encStt })
  | .expr obj => do
    let (astAnon, ptrAnon, encStt) := obj.anon.encode (← get).encodeState
    let (astMeta, ptrMeta, encStt) := obj.meta.encode encStt
    modifyGet fun stt => (⟨ptrAnon, ptrMeta⟩, { stt with
      irStore := { stt.irStore with
        exprAnon := stt.irStore.exprAnon.insert ptrAnon obj.anon,
        exprMeta := stt.irStore.exprMeta.insert ptrMeta obj.meta }
      exprAnon := stt.exprAnon.push $ ~[ToAST.toAST ptrAnon, astAnon]
      exprMeta := stt.exprMeta.push $ ~[ToAST.toAST ptrMeta, astMeta]
      encodeState := encStt })
  | .const obj => do
    let (astAnon, ptrAnon, encStt) := obj.anon.encode (← get).encodeState
    let (astMeta, ptrMeta, encStt) := obj.meta.encode encStt
    match obj.anon, obj.meta with
    -- Mutual definition/inductive blocks do not get added to the set of constants
    | .mutDefBlock .., .mutDefBlock ..
    | .mutIndBlock .., .mutIndBlock .. =>
      modifyGet fun stt => (⟨ptrAnon, ptrMeta⟩, { stt with
        irStore := { stt.irStore with
          constAnon := stt.irStore.constAnon.insert ptrAnon obj.anon,
          constMeta := stt.irStore.constMeta.insert ptrMeta obj.meta }
        constAnon := stt.constAnon.push $ ~[ToAST.toAST ptrAnon, astAnon]
        constMeta := stt.constMeta.push $ ~[ToAST.toAST ptrMeta, astMeta]
        encodeState := encStt })
    | _, _ =>
      let cid := ⟨ptrAnon, ptrMeta⟩
      let prtAnonAST := ToAST.toAST ptrAnon
      let prtMetaAST := ToAST.toAST ptrMeta
      modifyGet fun stt => (cid, { stt with
        irStore := { stt.irStore with
          constAnon := stt.irStore.constAnon.insert ptrAnon obj.anon,
          constMeta := stt.irStore.constMeta.insert ptrMeta obj.meta,
          consts    := stt.irStore.consts.insert cid }
        constAnon := stt.constAnon.push $ ~[prtAnonAST, astAnon]
        constMeta := stt.constMeta.push $ ~[prtMetaAST, astMeta]
        consts    := stt.consts.push    $ ~[prtAnonAST, prtMetaAST]
        encodeState := encStt })

/-- Adds data associated with a name to the cache -/
def addToCache (name : Name) (c : IR.BothConstScalar × TC.ConstIdx) : CompileM Unit :=
  modify fun stt => { stt with cache := stt.cache.insert name c }

/-- Adds a constant to the array of constants at a given index -/
def addToConsts (idx : TC.ConstIdx) (c : TC.Const) : CompileM Unit := do
  let tcStore := (← get).tcStore
  let consts := tcStore.consts
  if h : idx < consts.size then
    modify fun stt =>
      { stt with tcStore := { tcStore with consts := consts.set ⟨idx, h⟩ c } }
  else
    throw $ .invalidConstantIndex idx consts.size

end Yatima.Compiler
