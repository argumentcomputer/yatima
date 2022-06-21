import Lean
import Std

open Lean
open Std (HashSet)

namespace Yatima.Compiler

def uniteHashSets [BEq α] [Hashable α] (hs₁ hs₂ : HashSet α) : HashSet α :=
  if hs₁.size < hs₂.size then
    hs₁.fold (init := hs₂) fun acc a => acc.insert a
  else
    hs₂.fold (init := hs₁) fun acc a => acc.insert a

def getOpenReferencesInExpr (map : ConstMap) (mem : HashSet Name) :
    Expr → HashSet Name
  | .app e₁ e₂ .. =>
    uniteHashSets (getOpenReferencesInExpr map mem e₁)
      (getOpenReferencesInExpr map mem e₂)
  | .lam _ e₁ e₂ .. =>
    uniteHashSets (getOpenReferencesInExpr map mem e₁)
      (getOpenReferencesInExpr map mem e₂)
  | .forallE _ e₁ e₂ .. =>
    uniteHashSets (getOpenReferencesInExpr map mem e₁)
        (getOpenReferencesInExpr map mem e₂)
  | .letE _ e₁ e₂ e₃ .. =>
    uniteHashSets
      (uniteHashSets (getOpenReferencesInExpr map mem e₁)
        (getOpenReferencesInExpr map mem e₂))
      (getOpenReferencesInExpr map mem e₃)
  | .mdata _ e ..  => getOpenReferencesInExpr map mem e
  | .proj n _ e .. =>
    getOpenReferencesInExpr map (if map.contains n then mem else mem.insert n) e
  | .const n .. => if map.contains n then mem else mem.insert n
  | _ => mem

def getOpenReferencesInConst (map : ConstMap) : ConstantInfo → HashSet Name
  | .axiomInfo struct => getOpenReferencesInExpr map .empty struct.type
  | .thmInfo struct =>
      getOpenReferencesInExpr
        map (getOpenReferencesInExpr map .empty struct.type) struct.value
  | .opaqueInfo struct =>
      getOpenReferencesInExpr
        map (getOpenReferencesInExpr map .empty struct.type) struct.value
  | .defnInfo struct =>
      getOpenReferencesInExpr
        map (getOpenReferencesInExpr map .empty struct.type) struct.value
  | .ctorInfo struct => getOpenReferencesInExpr map .empty struct.type
  | .inductInfo struct => getOpenReferencesInExpr map .empty struct.type
  | .recInfo struct =>
    struct.rules.foldl
      (init := getOpenReferencesInExpr map .empty struct.type)
      fun acc r => getOpenReferencesInExpr map acc r.rhs
  | .quotInfo struct => getOpenReferencesInExpr map .empty struct.type

def hasOpenReferenceInExpr (openReferences : HashSet Name) : Expr → Bool
  | .app e₁ e₂ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
  | .lam _ e₁ e₂ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
  | .forallE _ e₁ e₂ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
  | .letE _ e₁ e₂ e₃ .. =>
    hasOpenReferenceInExpr openReferences e₁
      || hasOpenReferenceInExpr openReferences e₂
      || hasOpenReferenceInExpr openReferences e₃
  | .mdata _ e ..  => hasOpenReferenceInExpr openReferences e
  | .proj n _ e .. =>
    openReferences.contains n
      || hasOpenReferenceInExpr openReferences e
  | .const n .. => openReferences.contains n
  | _ => false

def hasOpenReferenceInConst (openReferences : HashSet Name) :
    ConstantInfo → Bool
  | .axiomInfo struct => hasOpenReferenceInExpr openReferences struct.type
  | .thmInfo struct =>
    hasOpenReferenceInExpr openReferences struct.type
      || hasOpenReferenceInExpr openReferences struct.value
  | .opaqueInfo struct =>
    hasOpenReferenceInExpr openReferences struct.type
      || hasOpenReferenceInExpr openReferences struct.value
  | .defnInfo struct =>
    hasOpenReferenceInExpr openReferences struct.type
      || hasOpenReferenceInExpr openReferences struct.value
  | .ctorInfo struct => hasOpenReferenceInExpr openReferences struct.type
  | .inductInfo struct => hasOpenReferenceInExpr openReferences struct.type
  | .recInfo struct =>
    struct.rules.foldl
      (init := hasOpenReferenceInExpr openReferences struct.type)
      fun acc r => acc || hasOpenReferenceInExpr openReferences struct.type
  | .quotInfo struct => hasOpenReferenceInExpr openReferences struct.type

def filterConstants (cs : ConstMap) : ConstMap :=
  let openReferences : HashSet Name := cs.fold (init := .empty)
    fun acc _ c => uniteHashSets acc $ getOpenReferencesInConst cs c
  Lean.List.toSMap $ cs.toList.filter fun (n, c) =>
    (!openReferences.contains n) && (!hasOpenReferenceInConst openReferences c)

end Yatima.Compiler
