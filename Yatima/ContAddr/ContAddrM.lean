import Yatima.ContAddr.ContAddrError
import Yatima.Common.ToLDON
import Yatima.Common.LightData
import Yatima.Common.IO

namespace Yatima.ContAddr

open Std (RBMap)
open IR

structure ContAddrState where
  env : Env
  commits : RBMap Const Lurk.F compare
  ldonHashState : Lurk.LDONHashState -- to speed up committing
  deriving Inhabited

def ContAddrState.init (env : Env) : ContAddrState :=
  ⟨env, default, default⟩

def ContAddrState.store (stt : ContAddrState) : Std.RBMap Lurk.F Const compare :=
  stt.commits.foldl (init := .empty) fun acc c f => acc.insert f c

structure ContAddrCtx where
  constMap : Lean.ConstMap
  univCtx  : List Name
  bindCtx  : List Name
  /-- The indices of the constants in their mutual block -/
  recrCtx  : Std.RBMap Name Nat compare
  quick    : Bool
  persist  : Bool
  deriving Inhabited

/-- Instantiates a `Yatima.ContAddr.ContAddrEnv` from a map of constants -/
def ContAddrCtx.init (map : Lean.ConstMap) (quick persist : Bool) : ContAddrCtx :=
  ⟨map, [], [], .empty, quick, persist⟩

abbrev ContAddrM := ReaderT ContAddrCtx $ ExceptT ContAddrError $
  StateT ContAddrState IO

def ContAddrM.run (constMap : Lean.ConstMap) (yenv : Env) (quick persist : Bool)
    (m : ContAddrM α) : IO $ Except ContAddrError ContAddrState := do
  let persist := if quick then false else persist
  match ← StateT.run (ReaderT.run m (.init constMap quick persist)) (.init yenv) with
  | (.ok _, stt) => return .ok stt
  | (.error e, _) => return .error e

def withBinder (name : Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

def withLevelsAndReset (levels : List Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c =>
    { c with univCtx := levels, bindCtx := [], recrCtx := .empty }

def withRecrs (recrCtx : RBMap Name Nat compare) :
    ContAddrM α → ContAddrM α :=
  withReader $ fun c => { c with recrCtx := recrCtx }

def withLevels (lvls : List Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c => { c with univCtx := lvls }

open System (FilePath) in
def commit (const : Const) : ContAddrM Lurk.F := do
  match (← get).commits.find? const with
  | some hash => pure hash
  | none =>
    if (← read).quick then
      let hash := .ofNat $ (Hashable.hash const).toNat
      modifyGet fun stt => (hash, { stt with
        commits := stt.commits.insert const hash })
    else
      let data : LightData := Encodable.encode const
      let path := COMMITSDIR / data.hash.data.toHex
      match ← loadData path with
      | some hash =>
        modifyGet fun stt => (hash, { stt with
          commits := stt.commits.insert const hash })
      | none =>
        let (hash, encStt) := const.toLDON.commit (← get).ldonHashState
        if (← read).persist then dumpData hash path
        modifyGet fun stt => (hash, { stt with
          commits := stt.commits.insert const hash
          ldonHashState := encStt })

@[inline] def addToEnv (name : Name) (hash : Lurk.F) : ContAddrM Unit :=
  modify fun stt => { stt with env := { stt.env with
    consts := stt.env.consts.insert name hash } }

end Yatima.ContAddr
