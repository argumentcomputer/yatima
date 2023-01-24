import Yatima.ContAddr.LightData
import Yatima.ContAddr.ContAddrError

namespace Yatima.ContAddr

open Std (RBMap)

open IR

structure ContAddrState where
  store : Yatima.Store
  env   : Yatima.Env
  deriving Inhabited

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
  StateT ContAddrState IO

def ContAddrM.run (ctx : ContAddrCtx) (ste : ContAddrState) (m : ContAddrM α) :
    IO $ Except ContAddrError ContAddrState := do
  match ← StateT.run (ReaderT.run m ctx) ste with
  | (.ok _,  ste) => return .ok ste
  | (.error e, _) => return .error e

def withBinder (name : Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c => ⟨c.constMap, c.univCtx, name :: c.bindCtx, c.recrCtx⟩

def withLevelsAndReset (levels : List Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c => ⟨c.constMap, levels, [], .empty⟩

def withRecrs (recrCtx : RBMap Name RecrCtxEntry compare) :
    ContAddrM α → ContAddrM α :=
  withReader $ fun c => ⟨c.constMap, c.univCtx, c.bindCtx, recrCtx⟩

def withLevels (lvls : List Name) : ContAddrM α → ContAddrM α :=
  withReader $ fun c => ⟨c.constMap, lvls, c.bindCtx, c.recrCtx⟩

def getFromRecrCtx (name : Name) : ContAddrM $ RecrCtxEntry := do
  match (← read).recrCtx.find? name with
  | some entry => pure entry
  | none => throw $ .notFoundInRecrCtx name

inductive StoreEntry : Type → Type
  | univ  : UnivAnon  → UnivMeta  → StoreEntry (Hash × Hash)
  | expr  : ExprAnon  → ExprMeta  → StoreEntry (Hash × Hash)
  | const : ConstAnon → ConstMeta → StoreEntry (Hash × Hash)

def addToStore : StoreEntry α → ContAddrM α
  | .univ anon meta =>
    let hashes := (hashUnivAnon anon, hashUnivMeta meta)
    modifyGet fun stt => (hashes, { stt with store := { stt.store with
      irUnivAnon := stt.store.irUnivAnon.insert hashes.1 anon
      irUnivMeta := stt.store.irUnivMeta.insert hashes.2 meta } })
  | .expr anon meta =>
    let hashes := (hashExprAnon anon, hashExprMeta meta)
    modifyGet fun stt => (hashes, { stt with store := { stt.store with
      irExprAnon := stt.store.irExprAnon.insert hashes.1 anon
      irExprMeta := stt.store.irExprMeta.insert hashes.2 meta } })
  | .const anon meta =>
    let hashes := (hashConstAnon anon, hashConstMeta meta)
    modifyGet fun stt => (hashes, { stt with store := { stt.store with
      irConstAnon := stt.store.irConstAnon.insert hashes.1 anon
      irConstMeta := stt.store.irConstMeta.insert hashes.2 meta } })

def addIRHashesToEnv (name : Name) (hs : Hash × Hash) : ContAddrM Unit :=
  modify fun stt => { stt with
    env := { stt.env with irHashes := stt.env.irHashes.insert name hs } }

end Yatima.ContAddr
