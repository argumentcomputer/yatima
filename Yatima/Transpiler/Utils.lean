import Yatima.Transpiler.TranspileM

namespace Yatima.Transpiler

open Yatima.Compiler

def StoreKey.find? : (key : StoreKey A) → TranspileM (Option A)
  | .univ  univCid => do
    let store := (← read).store
    match store.univ_anon.find? univCid.anon, store.univ_meta.find? univCid.meta with
    | some univAnon, some univMeta => pure $ some ⟨ univAnon, univMeta ⟩
    | _, _ => pure none
  | .expr  exprCid => do
    let store := (← read).store
    match store.expr_anon.find? exprCid.anon, store.expr_meta.find? exprCid.meta with
    | some exprAnon, some exprMeta => pure $ some ⟨ exprAnon, exprMeta ⟩
    | _, _ => pure none
  | .const constCid => do
    let store := (← read).store
    match store.const_anon.find? constCid.anon, store.const_meta.find? constCid.meta with
    | some constAnon, some constMeta => pure $ some ⟨ constAnon, constMeta ⟩
    | _, _ => pure none

def StoreKey.find! (key : StoreKey A) : TranspileM A := do
  let some value ← StoreKey.find? key | throw "Cannot find key in store"
  return value

/-- 
Return `List (Inductive × List Constructor × IntRecursor × List ExtRecursor)`
-/
def getMutualIndInfo (ind : Inductive) : 
    TranspileM $ List (Name × List Name × Name × List Name) := do
  let cache := (← read).cache
  let cid : ConstCid := ← match cache.find? ind.name with 
  | some (cid, _) => return cid
  | none => throw s!"{ind.name} not found in cache"
  let blockCid : ConstCid := ← match ← StoreKey.find! $ .const cid with 
  | ⟨.inductiveProj indAnon, .inductiveProj indMeta⟩ => 
    return ⟨indAnon.block, indMeta.block⟩
  | _ => throw s!"cid not found in store"
  match ← StoreKey.find! $ .const blockCid with 
  | ⟨.mutIndBlock blockAnon, .mutIndBlock blockMeta⟩ => 
    blockAnon.zip blockMeta |>.mapM fun (_, indMeta) => do 
      let indName := indMeta.name.proj₂
      let ctors := indMeta.ctors.map fun ctor => ctor.name.proj₂
      let mut intR : Name := `none
      let mut extRs : List Name := []
      for ⟨b, recr⟩ in indMeta.recrs do 
        match b with 
        | .Intr => intR := recr.name.proj₂ 
        | .Extr => extRs := recr.name.proj₂ :: extRs
      return (indName, ctors, intR, extRs)
  | _ => throw "blockCid not found in store"

/-- 
Return `List Definition`
-/
def getMutualDefInfo (defn : Definition) : TranspileM $ List Name := do 
  let cache := (← read).cache
  let cid : ConstCid := ← match cache.find? defn.name with 
  | some (cid, _) => return cid
  | none => throw s!"{defn.name} not found in cache"
  let blockCid : ConstCid := ← match ← StoreKey.find! $ .const cid with 
  | ⟨.definitionProj defAnon, .definitionProj defMeta⟩ => 
    return ⟨defAnon.block, defMeta.block⟩
  | _ => throw s!"cid not found in store"
  match ← StoreKey.find! $ .const blockCid with 
  | ⟨_, .mutDefBlock blockMeta⟩ => 
    let defs ← blockMeta.mapM fun defsMeta => do 
      return defsMeta.proj₂.map (·.name.proj₂)
    return defs.join
  | _ => throw "blockCid not found in store"

end Yatima.Transpiler

namespace List 

def last! [Inhabited α] : List α → α
| [] => panic! "empty list"
| [a] => a
| [_, b] => b
| _ :: _ :: l => last! l

end List 