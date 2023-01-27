import Yatima.ContAddr.ContAddrError
import Yatima.Common.Store
import Yatima.Common.LightData
import Yatima.Common.IO

namespace Yatima.ContAddr

open Std (RBMap)
open IR

structure ContAddrState where
  env : Env
  univData : RBMap (UnivAnon × UnivMeta)
    ((Hash × Hash) × (LightData × LightData)) compare
  exprData : RBMap (ExprAnon × ExprMeta)
    ((Hash × Hash) × (LightData × LightData)) compare
  constData : RBMap (ConstAnon × ConstMeta)
    ((Hash × Hash) × (LightData × LightData)) compare
  deriving Inhabited

def ContAddrState.init (env : Env) : ContAddrState :=
  ⟨env, default, default, default⟩

/-- Used for dump/load tests -/
def ContAddrState.storeAnon (stt : ContAddrState) : StoreAnon := ⟨
  stt.univData.foldl  (init := default) fun acc (u, _) ((h, _), _) => acc.insert h u,
  stt.exprData.foldl  (init := default) fun acc (e, _) ((h, _), _) => acc.insert h e,
  stt.constData.foldl (init := default) fun acc (c, _) ((h, _), _) => acc.insert h c⟩

/-- Used for dump/load tests -/
def ContAddrState.storeMeta (stt : ContAddrState) : StoreMeta := ⟨
  stt.univData.foldl  (init := default) fun acc (_, u) ((_, h), _) => acc.insert h u,
  stt.exprData.foldl  (init := default) fun acc (_, e) ((_, h), _) => acc.insert h e,
  stt.constData.foldl (init := default) fun acc (_, c) ((_, h), _) => acc.insert h c⟩

instance : Encodable LightData LightData String := ⟨id, pure⟩

def ContAddrState.dump (stt : ContAddrState) (envPath : System.FilePath) : IO Unit := do
  dumpData stt.env envPath
  stt.univData.forM fun _ ((anonHash, metaHash), (anonData, metaData)) => do
    dumpData anonData (UNIVANONDIR / anonHash.data.toHex) false
    dumpData metaData (UNIVMETADIR / metaHash.data.toHex) false
  stt.exprData.forM fun _ ((anonHash, metaHash), (anonData, metaData)) => do
    dumpData anonData (EXPRANONDIR / anonHash.data.toHex) false
    dumpData metaData (EXPRMETADIR / metaHash.data.toHex) false
  stt.constData.forM fun _ ((anonHash, metaHash), (anonData, metaData)) => do
    dumpData anonData (CONSTANONDIR / anonHash.data.toHex) false
    dumpData metaData (CONSTMETADIR / metaHash.data.toHex) false

/--
The type of entries for the `recrCtx`. It contains:
1. The index of the constant in the mutual block
2. The index in the list of weakly equal mutual definitions (N/A inductives)
-/
abbrev RecrCtxEntry := Nat × Option Nat

structure ContAddrCtx where
  constMap : Lean.ConstMap
  univCtx  : List Name
  bindCtx  : List Name
  recrCtx  : Std.RBMap Name RecrCtxEntry compare
  deriving Inhabited

/-- Instantiates a `Yatima.ContAddr.ContAddrEnv` from a map of constants -/
def ContAddrCtx.init (map : Lean.ConstMap) : ContAddrCtx :=
  ⟨map, [], [], .empty⟩

abbrev ContAddrM := ReaderT ContAddrCtx $ ExceptT ContAddrError $
  StateT ContAddrState Id

def ContAddrM.run (constMap : Lean.ConstMap) (yenv : Env) (m : ContAddrM α) :
    Except ContAddrError ContAddrState :=
  match StateT.run (ReaderT.run m (.init constMap)) (.init yenv) with
  | (.ok _, stt) => return stt
  | (.error e, _) => throw e

def withBinder (name : Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

def withLevelsAndReset (levels : List Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c =>
    { c with univCtx := levels, bindCtx := [], recrCtx := .empty }

def withRecrs (recrCtx : RBMap Name RecrCtxEntry compare) :
    ContAddrM α → ContAddrM α :=
  withReader $ fun c => { c with recrCtx := recrCtx }

def withLevels (lvls : List Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c => { c with univCtx := lvls }

inductive StoreEntry : Type → Type
  | univ  : UnivAnon  → UnivMeta  → StoreEntry (Hash × Hash)
  | expr  : ExprAnon  → ExprMeta  → StoreEntry (Hash × Hash)
  | const : ConstAnon → ConstMeta → StoreEntry (Hash × Hash)

@[specialize] def addToStore : StoreEntry α → ContAddrM α
  | .univ anon meta => do match (← get).univData.find? (anon, meta) with
    | some (hashes, _) => pure hashes
    | none =>
      let (anonData, anonHash) := hashUnivAnon anon
      let (metaData, metaHash) := hashUnivMeta meta
      let hashes := (anonHash, metaHash)
      modifyGet fun stt => (hashes, { stt with
        univData := stt.univData.insert (anon, meta)
          (hashes, (anonData, metaData)) })
  | .expr anon meta => do match (← get).exprData.find? (anon, meta) with
    | some (hashes, _) => pure hashes
    | none =>
      let (anonData, anonHash) := hashExprAnon anon
      let (metaData, metaHash) := hashExprMeta meta
      let hashes := (anonHash, metaHash)
      modifyGet fun stt => (hashes, { stt with
        exprData := stt.exprData.insert (anon, meta)
          (hashes, (anonData, metaData)) })
  | .const anon meta => do match (← get).constData.find? (anon, meta) with
    | some (hashes, _) => pure hashes
    | none =>
      let (anonData, anonHash) := hashConstAnon anon
      let (metaData, metaHash) := hashConstMeta meta
      let hashes := (anonHash, metaHash)
      modifyGet fun stt => (hashes, { stt with
        constData := stt.constData.insert (anon, meta)
          (hashes, (anonData, metaData)) })

@[inline] def addToEnv (name : Name) (hs : Hash × Hash) : ContAddrM Unit :=
  modify fun stt => { stt with env := { stt.env with
    consts := stt.env.consts.insert name hs } }

end Yatima.ContAddr
