import LightData
import Yatima.Datatypes.Const
import Yatima.Datatypes.Env

namespace Yatima.ContAddr

open IR

scoped notation "dec" x => Encodable.decode x

def partitionName (name : Name) : List (Either String Nat) :=
  let rec aux (acc : List (Either String Nat)) : Name → List (Either String Nat)
    | .str name s => aux ((.left s) :: acc) name
    | .num name n => aux ((.right n) :: acc) name
    | .anonymous  => acc
  aux [] name

instance : Encodable Name LightData where
  encode n := partitionName n
  decode x := do
    let parts : List (Either String Nat) ← dec x
    parts.foldlM (init := .anonymous) fun acc x => match x with
      | .left  s => pure $ acc.mkStr s
      | .right n => pure $ acc.mkNum n

instance : Encodable Literal LightData where
  encode
    | .strVal s => .cell #[false, s]
    | .natVal n => .cell #[true,  n]
  decode
    | .cell #[false, s] => return .strVal (← dec s)
    | .cell #[true,  n] => return .natVal (← dec n)
    | x => throw s!"expected either but got {x}"

instance : Encodable BinderInfo LightData where
  encode | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
  decode
    | 0 => pure .default
    | 1 => pure .implicit
    | 2 => pure .strictImplicit
    | 3 => pure .instImplicit
    | x => throw s!"Invalid encoding for BinderInfo: {x}"

instance : Encodable QuotKind LightData where
  encode | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
  decode
    | 0 => pure .type
    | 1 => pure .ctor
    | 2 => pure .lift
    | 3 => pure .ind
    | x => throw s!"Invalid encoding for QuotKind: {x}"

def univToLightData : Univ → LightData
  | .zero     => 0
  | .succ x   => .cell #[false, univToLightData x]
  | .var  x   => .cell #[true,  x]
  | .max  x y => .cell #[false, univToLightData x, univToLightData y]
  | .imax x y => .cell #[true,  univToLightData x, univToLightData y]

partial def lightDataToUniv : LightData → Except String Univ
  | 0 => pure .zero
  | .cell #[false, x] => return .succ (← lightDataToUniv x)
  | .cell #[true,  x] => return .var (← dec x)
  | .cell #[false, x, y] => return .max  (← lightDataToUniv x) (← lightDataToUniv y)
  | .cell #[true,  x, y] => return .imax (← lightDataToUniv x) (← lightDataToUniv y)
  | x => throw s!"Invalid encoding for Univ: {x}"

instance : Encodable Univ LightData where
  encode := univToLightData
  decode := lightDataToUniv

instance : Encodable Lurk.F LightData where
  encode x := x.val
  decode x := return (.ofNat $ ← dec x)

def exprToLightData : Expr → LightData
  | .sort x => .cell #[0, x]
  | .lit  x => .cell #[1,  x]
  | .lam  x => .cell #[2, exprToLightData x]
  | .var   x y => .cell #[0, x, y]
  | .const x y => .cell #[1, x, y]
  | .app   x y => .cell #[2, exprToLightData x, exprToLightData y]
  | .pi    x y => .cell #[4, exprToLightData x, exprToLightData y]
  | .proj  x y => .cell #[5, x, exprToLightData y]
  | .letE x y z => .cell #[false, exprToLightData x, exprToLightData y, exprToLightData z]

partial def lightDataToExpr : LightData → Except String Expr
  | .cell #[0, x] => return .sort (← lightDataToUniv x)
  | .cell #[1, x] => return .lit (← dec x)
  | .cell #[2, x] => return .lam (← lightDataToExpr x)
  | .cell #[0, x, y] => return .var (← dec x) (← dec y)
  | .cell #[1, x, y] => return .const (← dec x) (← dec y)
  | .cell #[2, x, y] => return .app (← lightDataToExpr x) (← lightDataToExpr y)
  | .cell #[4, x, y] => return .pi  (← lightDataToExpr x) (← lightDataToExpr y)
  | .cell #[5, x, y] => return .proj (← dec x) (← lightDataToExpr y)
  | .cell #[false, x, y, z] =>
    return .letE (← lightDataToExpr x) (← lightDataToExpr y) (← lightDataToExpr z)
  | x => throw s!"Invalid encoding for IR.Expr: {x}"

instance : Encodable Expr LightData where
  encode := exprToLightData
  decode := lightDataToExpr

instance : Encodable Constructor LightData where
  encode | ⟨a, b, c, d, e⟩ => .cell #[a, b, c, d, e]
  decode
    | .cell #[a, b, c, d, e] => return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | x => throw s!"Invalid encoding for IR.Constructor: {x}"

instance : Encodable RecursorRule LightData where
  encode | ⟨a, b, c⟩ => .cell #[a, b, c]
  decode
    | .cell #[a, b, c] => return ⟨← dec a, ← dec b, ← dec c⟩
    | x => throw s!"Invalid encoding for IR.RecursorRule: {x}"

instance : Encodable Definition LightData where
  encode | ⟨a, b, c, d⟩ => .cell #[a, b, c, d]
  decode
    | .cell #[a, b, c, d] => return ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | x => throw s!"Invalid encoding for IR.Definition: {x}"

instance : Encodable Recursor LightData where
  encode | ⟨a, b, c, d, e, f, g, h, i⟩ => .cell #[a, b, c, d, e, f, g, h, i]
  decode
    | .cell #[a, b, c, d, e, f, g, h, i] =>
      return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f, ← dec g, ← dec h, ← dec i⟩
    | x => throw s!"Invalid encoding for IR.Recursor: {x}"

instance : Encodable Inductive LightData where
  encode | ⟨a, b, c, d, e, f, g, h, i, j⟩ => .cell #[a, b, c, d, e, f, g, h, i, j]
  decode
    | .cell #[a, b, c, d, e, f, g, h, i, j] =>
      return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f, ← dec g,
        ← dec h, ← dec i, ← dec j⟩
    | x => throw s!"Invalid encoding for IR.Inductive: {x}"

instance : Encodable Const LightData where
  encode
    | .mutIndBlock x => .cell #[false, x]
    | .mutDefBlock x => .cell #[true,  x]
    | .axiom          ⟨a, b⟩ => .cell #[0, a, b]
    | .inductiveProj  ⟨a, b⟩ => .cell #[1, a, b]
    | .definitionProj ⟨a, b⟩ => .cell #[2, a, b]
    | .theorem         ⟨a, b, c⟩ => .cell #[0, a, b, c]
    | .opaque          ⟨a, b, c⟩ => .cell #[1, a, b, c]
    | .quotient        ⟨a, b, c⟩ => .cell #[2, a, b, c]
    | .constructorProj ⟨a, b, c⟩ => .cell #[3, a, b, c]
    | .recursorProj    ⟨a, b, c⟩ => .cell #[4, a, b, c]
    | .definition ⟨a, b, c, d⟩ => .cell #[false, a, b, c, d]
  decode
    | .cell #[false, x] => return .mutIndBlock (← dec x)
    | .cell #[true,  x] => return .mutDefBlock (← dec x)
    | .cell #[0, a, b] => return .axiom          ⟨← dec a, ← dec b⟩
    | .cell #[1, a, b] => return .inductiveProj  ⟨← dec a, ← dec b⟩
    | .cell #[2, a, b] => return .definitionProj ⟨← dec a, ← dec b⟩
    | .cell #[0, a, b, c] => return .theorem         ⟨← dec a, ← dec b, ← dec c⟩
    | .cell #[1, a, b, c] => return .opaque          ⟨← dec a, ← dec b, ← dec c⟩
    | .cell #[2, a, b, c] => return .quotient        ⟨← dec a, ← dec b, ← dec c⟩
    | .cell #[3, a, b, c] => return .constructorProj ⟨← dec a, ← dec b, ← dec c⟩
    | .cell #[4, a, b, c] => return .recursorProj    ⟨← dec a, ← dec b, ← dec c⟩
    | .cell #[false, a, b, c, d] => return .definition ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | x => throw s!"Invalid encoding for IR.Const: {x}"

instance [Encodable (Array (α × β)) LightData] [Ord α] :
    Encodable (Std.RBMap α β compare) LightData where
  encode x := (x.foldl (·.push (·, ·)) #[] : Array (α × β))
  decode x := return .ofArray (← dec x) _

instance [Encodable (Array α) LightData] [Ord α] :
    Encodable (Std.RBSet α compare) LightData where
  encode x := (x.foldl (·.push ·) #[] : Array α)
  decode x := return .ofArray (← dec x) _

instance : Encodable IR.Env LightData where
  encode | ⟨x, y⟩ => .cell #[x, y]
  decode
    | .cell #[x, y] => return ⟨← dec x, ← dec y⟩
    | x => throw s!"Invalid encoding for IR.Definition: {x}"

end Yatima.ContAddr
