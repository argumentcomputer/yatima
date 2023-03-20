import Yatima.ContAddr.ContAddrError
import Yatima.Common.ToLDON
import Yatima.Common.LightData
import Yatima.Common.IO
import Lurk.Scalar

namespace Yatima.ContAddr

open Std (RBMap)
open IR

structure ContAddrState where
  env : Env
  commits : RBMap Const Lurk.F compare
  ldonHashState : Lurk.Scalar.LDONHashState -- to speed up committing
  deriving Inhabited

def ContAddrState.init (ldonHashState : Lurk.Scalar.LDONHashState) : ContAddrState :=
  ⟨default, default, ldonHashState⟩

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
      let (hash, encStt) := const.toLDON.commit (← get).ldonHashState
      modifyGet fun stt => (hash, { stt with
        commits := stt.commits.insert const hash
        ldonHashState := encStt })

@[inline] def addConstToEnv (name : Name) (hash : Lurk.F) : ContAddrM Unit :=
  modify fun stt => { stt with env := { stt.env with
    consts := stt.env.consts.insert name hash } }

@[inline] def addBlockToEnv (hash : Lurk.F) : ContAddrM Unit :=
  modify fun stt => { stt with env := { stt.env with
    blocks := stt.env.blocks.insert hash } }

end Yatima.ContAddr
