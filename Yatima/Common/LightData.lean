import LightData
import Yatima.Datatypes.Const
import Yatima.Datatypes.Env
import Yatima.Datatypes.Lurk

@[extern "lean_byte_array_blake3"]
opaque ByteArray.blake3 : @& ByteArray → ByteVector 32

def LightData.hash (ld : LightData) : ByteVector 32 :=
  ld.toByteArray.blake3

namespace Yatima.ContAddr

open IR

scoped notation "dec" x => Encodable.decode x

def partitionName (name : Name) : List (Either String Nat) :=
  let rec aux (acc : List (Either String Nat)) : Name → List (Either String Nat)
    | .str name s => aux ((.left s) :: acc) name
    | .num name n => aux ((.right n) :: acc) name
    | .anonymous  => acc
  aux [] name

instance : Encodable Name LightData String where
  encode n := partitionName n
  decode x := do
    let parts : List (Either String Nat) ← dec x
    parts.foldlM (init := .anonymous) fun acc x => match x with
      | .left  s => pure $ acc.mkStr s
      | .right n => pure $ acc.mkNum n

instance : Encodable Literal LightData String where
  encode
    | .strVal s => .cell #[false, s]
    | .natVal n => .cell #[true,  n]
  decode
    | .cell #[false, s] => return .strVal (← dec s)
    | .cell #[true,  n] => return .natVal (← dec n)
    | x => throw s!"expected either but got {x}"

instance : Encodable BinderInfo LightData String where
  encode | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
  decode
    | 0 => pure .default
    | 1 => pure .implicit
    | 2 => pure .strictImplicit
    | 3 => pure .instImplicit
    | x => throw s!"Invalid encoding for BinderInfo: {x}"

instance : Encodable QuotKind LightData String where
  encode | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
  decode
    | 0 => pure .type
    | 1 => pure .ctor
    | 2 => pure .lift
    | 3 => pure .ind
    | x => throw s!"Invalid encoding for QuotKind: {x}"

def univToLightData : Univ → LightData
  | .zero     => false
  | .succ x   => .cell #[false, univToLightData x]
  | .var  x   => .cell #[true,  x]
  | .max  x y => .cell #[false, univToLightData x, univToLightData y]
  | .imax x y => .cell #[true,  univToLightData x, univToLightData y]

partial def lightDataToUniv : LightData → Except String Univ
  | false => pure .zero
  | .cell #[false, x] => return .succ (← lightDataToUniv x)
  | .cell #[true,  x] => return .var (← dec x)
  | .cell #[false, x, y] => return .max  (← lightDataToUniv x) (← lightDataToUniv y)
  | .cell #[true,  x, y] => return .imax (← lightDataToUniv x) (← lightDataToUniv y)
  | x => throw s!"Invalid encoding for Univ: {x}"

instance : Encodable Univ LightData String where
  encode := univToLightData
  decode := lightDataToUniv

instance : Encodable Lurk.F LightData String where
  encode x := x.val
  decode x := return (.ofNat $ ← dec x)

def exprToLightData : Expr → LightData
  | .sort x => .cell #[false, x]
  | .lit  x => .cell #[true,  x]
  | .var   x y => .cell #[0, x, y]
  | .const x y => .cell #[1, x, y]
  | .app   x y => .cell #[2, exprToLightData x, exprToLightData y]
  | .lam   x y => .cell #[3, exprToLightData x, exprToLightData y]
  | .pi    x y => .cell #[4, exprToLightData x, exprToLightData y]
  | .proj  x y => .cell #[5, x, exprToLightData y]
  | .letE x y z => .cell #[false, exprToLightData x, exprToLightData y, exprToLightData z]

partial def lightDataToExpr : LightData → Except String Expr
  | .cell #[false, x] => return .sort (← lightDataToUniv x)
  | .cell #[true,  x] => return .lit (← dec x)
  | .cell #[0, x, y] => return .var (← dec x) (← dec y)
  | .cell #[1, x, y] => return .const (← dec x) (← dec y)
  | .cell #[2, x, y] => return .app (← lightDataToExpr x) (← lightDataToExpr y)
  | .cell #[3, x, y] => return .lam (← lightDataToExpr x) (← lightDataToExpr y)
  | .cell #[4, x, y] => return .pi  (← lightDataToExpr x) (← lightDataToExpr y)
  | .cell #[5, x, y] => return .proj (← dec x) (← lightDataToExpr y)
  | .cell #[false, x, y, z] =>
    return .letE (← lightDataToExpr x) (← lightDataToExpr y) (← lightDataToExpr z)
  | x => throw s!"Invalid encoding for IR.Expr: {x}"

instance : Encodable Expr LightData String where
  encode := exprToLightData
  decode := lightDataToExpr

instance : Encodable Constructor LightData String where
  encode | ⟨a, b, c, d, e⟩ => .cell #[a, b, c, d, e]
  decode
    | .cell #[a, b, c, d, e] => return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | x => throw s!"Invalid encoding for IR.Constructor: {x}"

instance : Encodable RecursorRule LightData String where
  encode | ⟨a, b⟩ => .cell #[a, b]
  decode
    | .cell #[a, b] => return ⟨← dec a, ← dec b⟩
    | x => throw s!"Invalid encoding for IR.RecursorRule: {x}"

instance : Encodable Definition LightData String where
  encode | ⟨a, b, c, d⟩ => .cell #[a, b, c, d]
  decode
    | .cell #[a, b, c, d] => return ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | x => throw s!"Invalid encoding for IR.Definition: {x}"

instance : Encodable Recursor LightData String where
  encode | ⟨a, b, c, d, e, f, g, h, i⟩ => .cell #[a, b, c, d, e, f, g, h, i]
  decode
    | .cell #[a, b, c, d, e, f, g, h, i] =>
      return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f, ← dec g, ← dec h, ← dec i⟩
    | x => throw s!"Invalid encoding for IR.Recursor: {x}"

instance : Encodable Inductive LightData String where
  encode | ⟨a, b, c, d, e, f, g, h, i, j⟩ => .cell #[a, b, c, d, e, f, g, h, i, j]
  decode
    | .cell #[a, b, c, d, e, f, g, h, i, j] =>
      return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f, ← dec g,
        ← dec h, ← dec i, ← dec j⟩
    | x => throw s!"Invalid encoding for IR.Inductive: {x}"

instance : Encodable Const LightData String where
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

instance [h : Encodable (Array (α × β)) LightData String] [Ord α] :
    Encodable (Std.RBMap α β compare) LightData String where
  encode x := h.encode $ x.foldl (·.push (·, ·)) #[]
  decode x := return .ofArray (← dec x) _

instance : Encodable IR.Env LightData String where
  encode x := x.consts
  decode x := return ⟨← dec x⟩

section LDON

open Lurk

instance : Encodable Tag LightData String where
  encode x := x.toF
  decode x := do match Tag.ofF (← dec x) with
    | some t => return t
    | none => throw s!"Invalid encoding for Tag: {x}"

instance : Encodable ScalarPtr LightData String where
  encode | ⟨x, y⟩ => .cell #[x, y]
  decode
    | .cell #[x, y] => return ⟨← dec x, ← dec y⟩
    | x => throw s!"Invalid encoding for ScalarPtr: {x}"

instance : Encodable ScalarExpr LightData String where
  encode
    | .nil    => 0
    | .strNil => 1
    | .symNil => 2
    | .num  x => .cell #[false, x]
    | .char x => .cell #[true,  x]
    | .cons    x y => .cell #[0, x, y]
    | .strCons x y => .cell #[1, x, y]
    | .symCons x y => .cell #[2, x, y]
    | .comm    x y => .cell #[3, x, y]
  decode
    | 0 => return .nil
    | 1 => return .strNil
    | 2 => return .symNil
    | .cell #[false, x] => return .num  (← dec x)
    | .cell #[true,  x] => return .char (← dec x)
    | .cell #[0, x, y] => return .cons    (← dec x) (← dec y)
    | .cell #[1, x, y] => return .strCons (← dec x) (← dec y)
    | .cell #[2, x, y] => return .symCons (← dec x) (← dec y)
    | .cell #[3, x, y] => return .comm    (← dec x) (← dec y)
    | x => throw s!"Invalid encoding for ScalarExpr: {x}"

def LDONToLightData : LDON → LightData
  | .nil => false
  | .num x => .cell #[false, x]
  | .str x => .cell #[true,  x]
  | .cons x y => .cell #[false, LDONToLightData x, LDONToLightData y]

partial def lightDataToLDON : LightData → Except String LDON
  | false => return .nil
  | .cell #[false, x] => return .num (← dec x)
  | .cell #[true,  x] => return .str (← dec x)
  | .cell #[false, x, y] => return .cons (← lightDataToLDON x) (← lightDataToLDON y)
  | x => throw s!"Invalid encoding for LDON: {x}"

instance : Encodable LDON LightData String where
  encode := LDONToLightData
  decode := lightDataToLDON

instance : Encodable Char LightData String where
  encode x := x.toNat
  decode x := return .ofNat (← dec x)

instance : Encodable LDONHashState LightData String where
  encode | ⟨a, b, c⟩ => .cell #[a, b, c]
  decode
    | .cell #[a, b, c] => return ⟨← dec a, ← dec b, ← dec c⟩
    | x => throw s!"Invalid encoding for LDONHashState: {x}"

end LDON

end Yatima.ContAddr
