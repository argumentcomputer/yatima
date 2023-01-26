import Yatima.Datatypes.LightData
import Yatima.ContAddr.ContAddrError
import Yatima.Common.IO

namespace Yatima.ContAddr

open Std (RBMap)

open IR

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
  StateT Env IO

def ContAddrM.run (ctx : ContAddrCtx) (yenv : Env) (m : ContAddrM α) :
    IO $ Except ContAddrError Env := do
  match ← StateT.run (ReaderT.run m ctx) yenv with
  | (.ok _, yenv) => return .ok yenv
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

inductive StoreEntry : Type → Type
  | univ  : UnivAnon  → UnivMeta  → StoreEntry (Hash × Hash)
  | expr  : ExprAnon  → ExprMeta  → StoreEntry (Hash × Hash)
  | const : ConstAnon → ConstMeta → StoreEntry (Hash × Hash)

def addToStore : StoreEntry α → ContAddrM α
  | .univ anon meta => do
    let (anonData, anonHash) := hashUnivAnon anon
    let (metaData, metaHash) := hashUnivMeta meta
    persistData anonData (UNIVANONDIR / anonHash.data.toHex)
    persistData metaData (UNIVMETADIR / metaHash.data.toHex)
    return (anonHash, metaHash)
  | .expr anon meta => do
    let (anonData, anonHash) := hashExprAnon anon
    let (metaData, metaHash) := hashExprMeta meta
    persistData anonData (EXPRANONDIR / anonHash.data.toHex)
    persistData metaData (EXPRMETADIR / metaHash.data.toHex)
    return (anonHash, metaHash)
  | .const anon meta => do
    let (anonData, anonHash) := hashConstAnon anon
    let (metaData, metaHash) := hashConstMeta meta
    persistData anonData (CONSTANONDIR / anonHash.data.toHex)
    persistData metaData (CONSTMETADIR / metaHash.data.toHex)
    return (anonHash, metaHash)

@[inline] def addToEnv (name : Name) (hs : Hash × Hash) : ContAddrM Unit :=
  modify fun yenv => {yenv with consts := yenv.consts.insert name hs}

end Yatima.ContAddr
