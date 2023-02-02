import LightData
import Yatima.Datatypes.Const
import Yatima.Datatypes.Env

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

instance : Encodable ConstructorAnon LightData String where
  encode | ⟨a, b, c, d, e, f⟩ => .arr #[a, b, c, d, e, f]
  decode
    | .arr #[a, b, c, d, e, f] =>
      return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f⟩
    | x => throw s!"Invalid encoding for ConstructorAnon: {x}"

instance : Encodable ConstructorMeta LightData String where
  encode | ⟨a, b, c⟩ => .arr #[a, b, c]
  decode
    | .arr #[a, b, c] => return ⟨← dec a, ← dec b, ← dec c⟩
    | x => throw s!"Invalid encoding for ConstructorMeta: {x}"

instance : Encodable RecursorRuleAnon LightData String where
  encode | ⟨a, b⟩ => .prd (a, b)
  decode
    | .prd (a, b) => return ⟨← dec a, ← dec b⟩
    | x => throw s!"Invalid encoding for RecursorRuleAnon: {x}"

instance : Encodable RecursorRuleMeta LightData String where
  encode | ⟨a⟩ => a
  decode | a => return ⟨← dec a⟩

instance : Encodable RecursorAnon LightData String where
  encode | ⟨a, b, c, d, e, f, g, h, i⟩ => .arr #[a, b, c, d, e, f, g, h, i]
  decode
    | .arr #[a, b, c, d, e, f, g, h, i] =>
      return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f, ← dec g,
        ← dec h, ← dec i⟩
    | x => throw s!"Invalid encoding for RecursorAnon: {x}"

instance : Encodable RecursorMeta LightData String where
  encode | ⟨a, b, c, d⟩ => .arr #[a, b, c, d]
  decode
    | .arr #[a, b, c, d] => return ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | x => throw s!"Invalid encoding for RecursorMeta: {x}"

instance : Encodable DefinitionAnon LightData String where
  encode | ⟨a, b, c, d⟩ => .arr #[a, b, c, d]
  decode
    | .arr #[a, b, c, d] => return ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | x => throw s!"Invalid encoding for DefinitionAnon: {x}"

instance : Encodable DefinitionMeta LightData String where
  encode | ⟨a, b, c, d⟩ => .arr #[a, b, c, d]
  decode
    | .arr #[a, b, c, d] => return ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | x => throw s!"Invalid encoding for DefinitionMeta: {x}"

instance : Encodable InductiveAnon LightData String where
  encode | ⟨a, b, c, d, e, f, g, h, i⟩ => .arr #[a, b, c, d, e, f, g, h, i]
  decode
    | .arr #[a, b, c, d, e, f, g, h, i] =>
      return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f, ← dec g, ← dec h, ← dec i⟩
    | x => throw s!"Invalid encoding for InductiveAnon: {x}"

instance : Encodable InductiveMeta LightData String where
  encode | ⟨a, b, c, d, e⟩ => .arr #[a, b, c, d, e]
  decode
    | .arr #[a, b, c, d, e] => return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | x => throw s!"Invalid encoding for InductiveMeta: {x}"

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
    | .succ x   => .opt $ some x
    | .max x y  => .arr #[1, x, y]
    | .imax x y => .arr #[2, x, y]
    | .var n    => n
  decode
    | .opt none       => pure .zero
    | .opt $ some x   => return .succ (← dec x)
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
    | .definition ⟨a, b, c, d⟩         => .arr #[3, a, b, c, d]
    | .quotient ⟨a, b, c⟩              => .arr #[4, a, b, c]
    | .inductiveProj ⟨a, b, c, d⟩      => .arr #[5, a, b, c, d]
    | .constructorProj ⟨a, b, c, d, e⟩ => .arr #[6, a, b, c, d, e]
    | .recursorProj ⟨a, b, c, d, e⟩    => .arr #[7, a, b, c, d, e]
    | .definitionProj ⟨a, b, c, d⟩     => .arr #[8, a, b, c, d]
    | .mutDefBlock x                   => .eit $ .left x
    | .mutIndBlock x                   => .eit $ .right x
  decode
    | .arr #[0, a, b, c]       => return .axiom    ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[1, a, b, c]       => return .theorem  ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[2, a, b, c, d]    => return .opaque   ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[3, a, b, c, d]    => return .opaque   ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[4, a, b, c]       => return .quotient ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[5, a, b, c, d]    => return .inductiveProj   ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[6, a, b, c, d, e] => return .constructorProj ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | .arr #[7, a, b, c, d, e] => return .recursorProj    ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | .arr #[8, a, b, c, d]    => return .definitionProj  ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .eit $ .left  x          => return .mutDefBlock (← dec x)
    | .eit $ .right x          => return .mutIndBlock (← dec x)
    | x                        => throw s!"Invalid encoding for ConstAnon: {x}"

instance : Encodable ConstMeta LightData String where
  encode
    | .axiom ⟨a, b, c⟩                 => .arr #[0, a, b, c]
    | .theorem ⟨a, b, c, d⟩            => .arr #[1, a, b, c, d]
    | .opaque ⟨a, b, c, d⟩             => .arr #[2, a, b, c, d]
    | .definition ⟨a, b, c, d⟩      => .arr #[3, a, b, c, d]
    | .quotient ⟨a, b, c⟩              => .arr #[4, a, b, c]
    | .inductiveProj ⟨a, b, c, d⟩      => .arr #[5, a, b, c, d]
    | .constructorProj ⟨a, b, c, d⟩    => .arr #[6, a, b, c, d]
    | .recursorProj ⟨a, b, c, d⟩       => .arr #[7, a, b, c, d]
    | .definitionProj ⟨a, b, c, d, e⟩  => .arr #[8, a, b, c, d, e]
    | .mutDefBlock x                   => .eit $ .left x
    | .mutIndBlock x                   => .eit $ .right x
  decode
    | .arr #[0, a, b, c]    => return .axiom    ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[1, a, b, c, d] => return .theorem  ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[2, a, b, c, d] => return .opaque   ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[3, a, b, c]    => return .quotient ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[4, a, b, c, d]    => return .inductiveProj   ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[5, a, b, c, d]    => return .constructorProj ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[6, a, b, c, d]    => return .recursorProj    ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[7, a, b, c, d, e] => return .definitionProj  ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | .eit $ .left  x          => return .mutDefBlock (← dec x)
    | .eit $ .right x          => return .mutIndBlock (← dec x)
    | x                        => throw s!"Invalid encoding for ConstMeta: {x}"

def hashUnivAnon (x : UnivAnon) : LightData × Hash :=
  let x := Encodable.encode x; (x, x.hash)

def hashExprAnon (x : ExprAnon) : LightData × Hash :=
  let x := Encodable.encode x; (x, x.hash)

def hashConstAnon (x : ConstAnon) : LightData × Hash :=
  let x := Encodable.encode x; (x, x.hash)

def hashUnivMeta (x : UnivMeta) : LightData × Hash :=
  let x := Encodable.encode x; (x, x.hash)

def hashExprMeta (x : ExprMeta) : LightData × Hash :=
  let x := Encodable.encode x; (x, x.hash)

def hashConstMeta (x : ConstMeta) : LightData × Hash :=
  let x := Encodable.encode x; (x, x.hash)

open TC
open Lurk (F LDONHashState)

def univToLightData : Univ → LightData
  | .zero     => .opt none
  | .succ x   => .opt $ some (univToLightData x)
  | .max x y  => .arr #[0, univToLightData x, univToLightData y]
  | .imax x y => .arr #[1, univToLightData x, univToLightData y]
  | .var x    => x

partial def lightDataToUniv : LightData → Except String Univ
  | .opt none       => pure .zero
  | .opt $ some x   => return .succ (← lightDataToUniv x)
  | .arr #[0, x, y] => return .max  (← lightDataToUniv x) (← lightDataToUniv y)
  | .arr #[1, x, y] => return .imax (← lightDataToUniv x) (← lightDataToUniv y)
  | x               => return .var  (← dec x)

instance : Encodable Univ LightData String where
  encode := univToLightData
  decode := lightDataToUniv

instance : Encodable F LightData String where
  encode x := x.val.toByteArrayLE
  decode
    | .byt bytes => return .ofNat bytes.asLEtoNat
    | x => throw s!"expected bytes but got {x}"

def exprToLightData : Expr → LightData
  | .sort x     => .prd (0, x)
  | .lit x      => .prd (1, x)
  | .var x      => .prd (2, x)
  | .const x y  => .arr #[3, x, y]
  | .app x y    => .arr #[4, exprToLightData x, exprToLightData y]
  | .lam x y    => .arr #[5, exprToLightData x, exprToLightData y]
  | .pi  x y    => .arr #[6, exprToLightData x, exprToLightData y]
  | .letE x y z => .arr #[7, exprToLightData x, exprToLightData y, exprToLightData z]
  | .proj x y   => .arr #[8, x, exprToLightData y]

partial def lightDataToExpr : LightData → Except String Expr
  | .prd (0, x) => return .sort (← lightDataToUniv x)
  | .prd (1, x) => return .lit (← dec x)
  | .prd (2, x) => return .var (← dec x)
  | .arr #[3, x, y] => return .const (← dec x) (← dec y)
  | .arr #[4, x, y] => return .app (← lightDataToExpr x) (← lightDataToExpr y)
  | .arr #[5, x, y] => return .lam (← lightDataToExpr x) (← lightDataToExpr y)
  | .arr #[6, x, y] => return .pi  (← lightDataToExpr x) (← lightDataToExpr y)
  | .arr #[7, x, y, z] => return .letE (← lightDataToExpr x) (← lightDataToExpr y) (← lightDataToExpr z)
  | .arr #[8, x, y] => return .proj (← dec x) (← lightDataToExpr y)
  | x => throw s!"Invalid encoding for TC.Expr: {x}"

instance : Encodable Expr LightData String where
  encode := exprToLightData
  decode := lightDataToExpr

instance : Encodable Constructor LightData String where
  encode | ⟨a, b, c, d, e, f⟩ => .arr #[a, b, c, d, e, f]
  decode
    | .arr #[a, b, c, d, e, f] => return ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e, ← dec f⟩
    | x => throw s!"Invalid encoding for TC.Constructor: {x}"

instance : Encodable RecursorRule LightData String where
  encode | ⟨a, b⟩ => .prd (a, b)
  decode
    | .prd (a, b) => return ⟨← dec a, ← dec b⟩
    | x => throw s!"Invalid encoding for TC.Constructor: {x}"

instance : Encodable Const LightData String where
  encode
    | .axiom ⟨a, b, c⟩     => .arr #[0, a, b, c]
    | .theorem ⟨a, b, c⟩   => .arr #[1, a, b, c]
    | .opaque ⟨a, b, c, d⟩ => .arr #[2, a, b, c, d]
    | .quotient ⟨a, b, c⟩  => .arr #[3, a, b, c]
    | .inductive ⟨a, b, c, d, e, f, g, h, i, j⟩   => .arr #[4, a, b, c, d, e, f, g, h, i, j]
    | .recursor ⟨a, b, c, d, e, f, g, h, i, j, l⟩ => .arr #[5, a, b, c, d, e, f, g, h, i, j, l]
    | .definition ⟨a, b, c, d, e⟩                 => .arr #[6, a, b, c, d, e]
    | .constructor x => .opt $ some x
  decode
    | .arr #[0, a, b, c] => return .axiom ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[1, a, b, c] => return .theorem ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[2, a, b, c, d] => return .opaque ⟨← dec a, ← dec b, ← dec c, ← dec d⟩
    | .arr #[3, a, b, c] => return .quotient ⟨← dec a, ← dec b, ← dec c⟩
    | .arr #[4, a, b, c, d, e, f, g, h, i, j] =>
      return .inductive ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e,
        ← dec f, ← dec g, ← dec h, ← dec i, ← dec j⟩
    | .arr #[5, a, b, c, d, e, f, g, h, i, j, l] =>
      return .recursor ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e,
        ← dec f, ← dec g, ← dec h, ← dec i, ← dec j, ← dec l⟩
    | .arr #[6, a, b, c, d, e] =>
      return .definition ⟨← dec a, ← dec b, ← dec c, ← dec d, ← dec e⟩
    | .opt $ some x => return .constructor (← dec x)
    | x => throw s!"Invalid encoding for TC.Const: {x}"

instance : Encodable LDONHashState LightData String where
  encode := default -- TODO
  decode := default -- TODO

instance [h : Encodable (Array (α × β)) LightData String] [Ord α] :
    Encodable (Std.RBMap α β compare) LightData String where
  encode x := h.encode ⟨x.toList⟩
  decode x := return .ofArray (← dec x) _

instance : Encodable IR.Env LightData String where
  encode x := x.consts
  decode | x => return ⟨← dec x⟩

end Yatima.ContAddr
