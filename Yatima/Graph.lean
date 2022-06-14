import Lean 

namespace Lean

namespace List

def eraseDup [BEq α] : List α → List α
  | [] => []
  | x::xs => 
    let exs := eraseDup xs
    if exs.contains x then exs else x::exs

end List

open Std (RBMap)

instance : Ord Name :=
 { compare := fun x y => compare (toString x) (toString y) }

abbrev ReferenceMap := RBMap Name (List Name) Ord.compare

def ReferenceMap.empty := @RBMap.empty Name (List Name) Ord.compare

instance : Inhabited ReferenceMap := 
  { default := ReferenceMap.empty }

mutual 

  partial def getExprRefs (expr : Expr) : List Name :=
    match expr with 
    | .const name _ _ => [name]
    | .app func arg _ => 
      getExprRefs func ++  getExprRefs arg
    | .lam name type body _ => 
      getExprRefs type ++  getExprRefs body
    | .forallE name type body _ => 
      getExprRefs type ++  getExprRefs body
    | .letE  name type body exp _ => 
      getExprRefs type ++  getExprRefs body ++ getExprRefs exp
    | .proj name idx exp _ => getExprRefs exp
    | _ => []

  partial def getConstRefs (const : ConstantInfo) : List Name :=
    match const with 
    | .axiomInfo  val => getExprRefs val.type
    | .defnInfo   val => 
      getExprRefs val.type ++ getExprRefs val.value
    | .thmInfo    val => 
      getExprRefs val.type ++ getExprRefs val.value
    | .opaqueInfo val => 
      getExprRefs val.type ++ getExprRefs val.value
    | .ctorInfo   val => 
      val.induct :: getExprRefs val.type
    | .inductInfo val => 
      getExprRefs val.type ++ val.ctors ++ val.all
    | .recInfo    val => 
      getExprRefs val.type ++ val.all ++ val.rules.map RecursorRule.ctor
    | .quotInfo   val => getExprRefs val.type

end

def referenceMap (constMap : ConstMap) : ReferenceMap :=
  SMap.fold 
    (fun acc name const => acc.insert name $ List.eraseDup $ getConstRefs const) 
    ReferenceMap.empty 
    constMap

instance : ToString ReferenceMap := 
 { toString := fun refs => toString refs.toList }

-- def detectCycles (constMap : ConstMap) : List (List Name) := sorry

end Lean