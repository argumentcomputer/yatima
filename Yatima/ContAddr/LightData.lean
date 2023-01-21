import LightData
import Yatima.Datatypes.Store

namespace Yatima.ContAddr

open IR

instance : Encodable Hash LightData String where
  encode x := .lnk x
  decode | .lnk x => pure x | x => throw s!"Expected a link but got {x}"

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
    | .strVal s => .eit (.left s)
    | .natVal n => .eit (.right n)
  decode
    | .eit (.left s)  => return .strVal (← dec s)
    | .eit (.right n) => return .natVal (← dec n)
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

instance : Encodable DefinitionSafety LightData String where
  encode | .unsafe => 0 | .safe => 1 | .partial => 2
  decode
    | 0 => pure .unsafe
    | 1 => pure .safe
    | 2 => pure .partial
    | x => throw s!"Invalid encoding for DefinitionSafety: {x}"

instance : Encodable DefinitionAnon LightData String where
  encode := sorry
  decode := sorry

instance : Encodable InductiveAnon LightData String where
  encode := sorry
  decode := sorry

instance : Encodable UnivAnon LightData String where
  encode
    | .zero     => .opt none
    | .max x y  => .arr #[0, x, y]
    | .imax x y => .arr #[1, x, y]
    | .succ x   => x
    | .var x    => x
  decode
    | .opt none       => pure .zero
    | .arr #[0, x, y] => return .max  (← dec x) (← dec y)
    | .arr #[1, x, y] => return .imax (← dec x) (← dec y)
    | x@(.lnk _)      => return .succ (← dec x)
    | x               => return .var  (← dec x)

instance : Encodable UnivMeta LightData String where
  encode
    | .zero     => .opt none
    | .succ x   => .prd (0, x)
    | .max x y  => .arr #[1, x, y]
    | .imax x y => .arr #[2, x, y]
    | .var n    => n
  decode
    | .opt none       => pure .zero
    | .prd (0, x)     => return .succ (← dec x)
    | .arr #[1, x, y] => return .max  (← dec x) (← dec y)
    | .arr #[2, x, y] => return .imax (← dec x) (← dec y)
    | x               => return .var  (← dec x)

instance : Encodable ExprAnon LightData String where
  encode
    | .sort x     => x
    | .lit x      => x
    | .var x y    => .arr #[0, x, y]
    | .const x y  => .arr #[1, x, y]
    | .app x y    => .arr #[2, x, y]
    | .lam x y    => .arr #[3, x, y]
    | .pi  x y    => .arr #[4, x, y]
    | .letE x y z => .arr #[5, x, y, z]
    | .proj x y   => .arr #[6, x, y]
  decode
    | .arr #[0, x, y]    => return .var   (← dec x) (← dec y)
    | .arr #[1, x, y]    => return .const (← dec x) (← dec y)
    | .arr #[2, x, y]    => return .app   (← dec x) (← dec y)
    | .arr #[3, x, y]    => return .lam   (← dec x) (← dec y)
    | .arr #[4, x, y]    => return .pi    (← dec x) (← dec y)
    | .arr #[5, x, y, z] => return .letE  (← dec x) (← dec y) (← dec z)
    | .arr #[6, x, y]    => return .proj  (← dec x) (← dec y)
    | x@(.eit _)         => return .lit   (← dec x)
    | x                  => return .sort  (← dec x)

instance : Encodable ExprMeta LightData String where
  encode
    | .var x y z    => .arr #[0, x, y, z]
    | .const x y    => .arr #[1, x, y]
    | .app x y      => .arr #[2, x, y]
    | .lam a b c d  => .arr #[3, a, b, c, d]
    | .pi  a b c d  => .arr #[4, a, b, c, d]
    | .letE a b c d => .arr #[5, a, b, c, d]
    | .sort x       => .eit $ .left  x
    | .proj x       => .eit $ .right x
    | .lit          => .opt none
  decode
    | .arr #[0, x, y, z]    => return .var   (← dec x) (← dec y) (← dec z)
    | .arr #[1, x, y]       => return .const (← dec x) (← dec y)
    | .arr #[2, x, y]       => return .app   (← dec x) (← dec y)
    | .arr #[3, a, b, c, d] => return .lam   (← dec a) (← dec b) (← dec c) (← dec d)
    | .arr #[4, a, b, c, d] => return .pi    (← dec a) (← dec b) (← dec c) (← dec d)
    | .arr #[5, a, b, c, d] => return .letE  (← dec a) (← dec b) (← dec c) (← dec d)
    | .eit $ .left  x       => return .sort  (← dec x)
    | .eit $ .right x       => return .proj  (← dec x)
    | .opt none             => pure .lit
    | x                     => throw s!"Invalid encoding for ExprMeta: {x}"

instance : Encodable ConstAnon LightData String where
  encode
    | .axiom ⟨a, b, c⟩                 => .arr #[0, a, b, c]
    | .theorem ⟨a, b, c⟩               => .arr #[1, a, b, c]
    | .opaque ⟨a, b, c, d⟩             => .arr #[2, a, b, c, d]
    | .quotient ⟨a, b, c⟩              => .arr #[3, a, b, c]
    | .inductiveProj ⟨a, b, c, d⟩      => .arr #[4, a, b, c, d]
    | .constructorProj ⟨a, b, c, d, e⟩ => .arr #[5, a, b, c, d, e]
    | .recursorProj ⟨a, b, c, d, e⟩    => .arr #[6, a, b, c, d, e]
    | .definitionProj ⟨a, b, c, d⟩     => .arr #[7, a, b, c, d]
    | .mutDefBlock x                   => .eit $ .left x
    | .mutIndBlock x                   => .eit $ .right x
  decode
    | .arr #[0, a, b, c]       => return .axiom    ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[1, a, b, c]       => return .theorem  ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[2, a, b, c, d]    => return .opaque   ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[3, a, b, c]       => return .quotient ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[4, a, b, c, d]    => return .inductiveProj   ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[5, a, b, c, d, e] => return .constructorProj ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | .arr #[6, a, b, c, d, e] => return .recursorProj    ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | .arr #[7, a, b, c, d]    => return .definitionProj  ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .eit $ .left  x          => return .mutDefBlock (← dec x)
    | .eit $ .right x          => return .mutIndBlock (← dec x)
    | x                        => throw s!"Invalid encoding for ConstAnon: {x}"

instance : Encodable ConstMeta LightData String := sorry

def hashUnivAnon (x : UnivAnon) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashExprAnon (x : ExprAnon) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashConstAnon (x : ConstAnon) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashUnivMeta (x : UnivMeta) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashExprMeta (x : ExprMeta) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

def hashConstMeta (x : ConstMeta) : ByteVector 32 :=
  (Encodable.encode x : LightData).hash

end Yatima.ContAddr
