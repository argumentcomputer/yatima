import Std.Data.RBTree
import Yatima.Datatypes.Name
import Yatima.Transpiler.TranspileM

namespace Yatima.Transpiler

open Std (RBTree)

/--
List of valid characters for Lurk identifiers. The order is shuffled to
avoid an unbalanced `RBTree`.
-/
def validCharsTree : RBTree Char compare :=
  RBTree.ofList [
    'e', 'f', '6', '7', 'C', 'D', 'E', 'F',
    'G', 'H', '8', '9', 'y', 'z', '2', '3',
    'm', 'n', 'W', 'X', 'A', 'B', '4', '5',
    'M', 'N', 's', 't', 'o', 'p', 'i', 'j',
    'k', 'l', 'Y', 'Z', 'S', 'T', 'g', 'h',
    'I', 'J', 'a', 'b', 'K', 'L', 'O', 'P',
    'U', 'V', '0', '1', 'u', 'v', 'c', 'd',
    'q', 'r', 'w', 'x', 'Q', 'R', '-', ':',
    '_']

/-- Generates a sequence of valid characters in Lurk from a given character. -/
def charToValidChars (c : Char) : List Char :=
  if validCharsTree.contains c then [c]
  else s!"--{charToHex c}--".replace "*" ":" |>.data

/-- Turns a `Name` into a valid variable identifier in Lurk. -/
def fixName (name : Name) (pretty := true) : String :=
  if pretty then 
    toString name 
  else 
    let name := name.toString.replace "." "_" -- |>.replace "_" "??" FIX: If they haven't merged the change yet, we need to revist this.
    let charsArray : Array Char := name.foldl (init := #[]) fun acc c =>
      acc.append ⟨charToValidChars c⟩
    ⟨charsArray.data⟩

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
  | none => throw ""
  let blockCid : ConstCid := ← match ← StoreKey.find! $ .const cid with 
  | ⟨.inductiveProj indAnon, .inductiveProj indMeta⟩ => 
    return ⟨indAnon.block, indMeta.block⟩
  | _ => throw ""
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
  | _ => throw ""

end Yatima.Transpiler
