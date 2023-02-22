import Yatima.ContAddr.ContAddrError
import Yatima.Common.LightData
import Yatima.Common.IO

namespace Yatima.ContAddr

open Std (RBMap)
open IR

structure ContAddrState where
  env : Env
  univData  : RBMap Univ  (Lurk.F × LightData) compare
  exprData  : RBMap Expr  (Lurk.F × LightData) compare
  constData : RBMap Const (Lurk.F × LightData) compare
  deriving Inhabited

def ContAddrState.init (env : Env) : ContAddrState :=
  ⟨env, default, default, default⟩

-- /-- Used for dump/load tests -/
-- def ContAddrState.storeAnon (stt : ContAddrState) : StoreAnon := ⟨
--   stt.univData.foldl  (init := default) fun acc (u, _) ((h, _), _) => acc.insert h u,
--   stt.exprData.foldl  (init := default) fun acc (e, _) ((h, _), _) => acc.insert h e,
--   stt.constData.foldl (init := default) fun acc (c, _) ((h, _), _) => acc.insert h c⟩

-- /-- Used for dump/load tests -/
-- def ContAddrState.storeMeta (stt : ContAddrState) : StoreMeta := ⟨
--   stt.univData.foldl  (init := default) fun acc (_, u) ((_, h), _) => acc.insert h u,
--   stt.exprData.foldl  (init := default) fun acc (_, e) ((_, h), _) => acc.insert h e,
--   stt.constData.foldl (init := default) fun acc (_, c) ((_, h), _) => acc.insert h c⟩

instance : Encodable LightData LightData String := ⟨id, pure⟩

def ContAddrState.dump (stt : ContAddrState) (envPath : System.FilePath) : IO Unit := do
  mkCADirs
  dumpData stt.env envPath
  stt.univData.forM  fun _ (hash, data) => dumpData data (UNIVDIR  / hash.asHex) false
  stt.exprData.forM  fun _ (hash, data) => dumpData data (EXPRDIR  / hash.asHex) false
  stt.constData.forM fun _ (hash, data) => dumpData data (CONSTDIR / hash.asHex) false

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
  quick    : Bool
  deriving Inhabited

/-- Instantiates a `Yatima.ContAddr.ContAddrEnv` from a map of constants -/
def ContAddrCtx.init (map : Lean.ConstMap) (quick : Bool) : ContAddrCtx :=
  ⟨map, [], [], .empty, quick⟩

abbrev ContAddrM := ReaderT ContAddrCtx $ ExceptT ContAddrError $
  StateT ContAddrState Id

def ContAddrM.run (constMap : Lean.ConstMap) (yenv : Env) (quick : Bool)
    (m : ContAddrM α) : Except ContAddrError ContAddrState :=
  match StateT.run (ReaderT.run m (.init constMap quick)) (.init yenv) with
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
  | univ  : Univ  → StoreEntry Lurk.F
  | expr  : Expr  → StoreEntry Lurk.F
  | const : Const → StoreEntry Lurk.F

@[specialize] def addToStore : StoreEntry α → ContAddrM α
  | .univ obj => do match (← get).univData.find? obj with
    | some (hash, _) => pure hash
    | none =>
      let data := Encodable.encode obj
      let hash := sorry
      modifyGet fun stt => (hash, { stt with
        univData := stt.univData.insert obj (hash, data) })
  | .expr obj => do match (← get).exprData.find? obj with
    | some (hash, _) => pure hash
    | none =>
      let data := Encodable.encode obj
      let hash := sorry
      modifyGet fun stt => (hash, { stt with
        exprData := stt.exprData.insert obj (hash, data) })
  | .const obj => do match (← get).constData.find? obj with
    | some (hash, _) => pure hash
    | none =>
      let data := Encodable.encode obj
      let hash := sorry
      modifyGet fun stt => (hash, { stt with
        constData := stt.constData.insert obj (hash, data) })

@[inline] def addToEnv (name : Name) (hash : Lurk.F) : ContAddrM Unit :=
  modify fun stt => { stt with env := { stt.env with
    consts := stt.env.consts.insert name hash } }

end Yatima.ContAddr
