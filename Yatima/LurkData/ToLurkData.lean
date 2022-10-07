import Yatima.Datatypes.Store
import Yatima.Datatypes.Cid
import Yatima.LurkData.Move

/-!
We follow the convention of `Yatima.IR.<object>.toLurk.Expr`
-/

open Lurk Expr ToExpr

namespace Lurk.Expr 

def num   (n : Fin N)  : Lurk.Expr := .lit $ .num n
def nat   (n : Nat)    : Lurk.Expr := .lit $ .num (Fin.ofNat n)
def int   (n : Fin N)  : Lurk.Expr := .lit $ .num (Fin.ofInt n)
def u8    (n : UInt8)  : Lurk.Expr := nat n.val
def u16   (n : UInt16) : Lurk.Expr := nat n.val
def u32   (n : UInt32) : Lurk.Expr := nat n.val
def u64   (n : UInt64) : Lurk.Expr := nat n.val
def usize (n : USize)  : Lurk.Expr := nat n.val

instance : ToExpr Bool where toExpr
  | false => .lit .nil
  | true  => .lit .t

instance [ToExpr α] [ToExpr β] : ToExpr (α ⊕ β) where toExpr
  | .inl a => toExpr a
  | .inr b => toExpr b

instance [ToExpr α] : ToExpr (Option α) where toExpr
  | none   => .lit .nil
  | some a => toExpr a

instance [ToExpr α] [ToExpr β] : ToExpr (α × β) where
  toExpr x := mkList [toExpr x.1, toExpr x.2]
  
instance [ToExpr α] : ToExpr (List α) where
  toExpr es := .mkList $ es.map toExpr
  
instance [ToExpr α] : ToExpr (Array α) where
  toExpr es := .mkList $ es.toList.map toExpr
  
instance [Ord α] [ToExpr α] [ToExpr β] : ToExpr (Std.RBMap α β compare) where
  toExpr es := .mkList $ es.toList.map toExpr
  
instance [Ord α] [ToExpr α] : ToExpr (Std.RBTree α compare) where
  toExpr es := .mkList $ es.toList.map toExpr

end Lurk.Expr 

namespace Yatima
namespace IR 

-- TODO: this seems wrong

-- TODO: after `.comm` gets bumped
instance : ToExpr (UnivCid  k) where toExpr u := .comm $ .num u.data
instance : ToExpr (ExprCid  k) where toExpr u := .comm $ .num u.data
instance : ToExpr (ConstCid k) where toExpr u := .comm $ .num u.data

instance : ToExpr BinderInfo where toExpr
  | .default        => toExpr 0
  | .implicit       => toExpr 1
  | .strictImplicit => toExpr 2
  | .instImplicit   => toExpr 3
  | .auxDecl        => toExpr 4

instance : ToExpr Literal where toExpr
  | .natVal n => toExpr n
  | .strVal s => toExpr s

instance : ToExpr DefinitionSafety where toExpr
  | .safe    => toExpr 0
  | .unsafe  => toExpr 1
  | .partial => toExpr 2

instance [ToExpr α] [ToExpr β] : ToExpr (Split α β k) where toExpr
  | .injₗ a => .mkList [toExpr 0, toExpr a]
  | .injᵣ b => .mkList [toExpr 1, toExpr b]

instance : ToExpr Unit where toExpr
  | .unit => .lit .nil

instance : (k : Kind) → ToExpr (RecursorRule k)
  | .anon => { toExpr := fun | .mk c f r => .mkList [toExpr c, toExpr f, toExpr r] }
  | .meta => { toExpr := fun | .mk c f r => .mkList [toExpr c, toExpr f, toExpr r] }

instance : ToExpr (Recursor b k) where toExpr
  | .mk n l ty p i m m' rs k => 
    .mkList [
      toExpr n, 
      toExpr l, 
      toExpr ty, 
      toExpr p, 
      toExpr i, 
      toExpr m, 
      toExpr m', 
      toExpr rs, 
      toExpr k ]

instance : ToExpr (Sigma (Recursor · k)) where toExpr
  | .mk b (.mk n l ty p i m m' rs k) => 
    .mkList [
      toExpr (b : Bool), 
      toExpr n, 
      toExpr l, 
      toExpr ty, 
      toExpr p, 
      toExpr i, 
      toExpr m, 
      toExpr m', 
      toExpr rs, 
      toExpr k ]

instance : ToExpr (Constructor k) where toExpr
  | .mk n ty l i p f r s => 
    .mkList [
      toExpr n, 
      toExpr ty, 
      toExpr l, 
      toExpr i, 
      toExpr p, 
      toExpr f, 
      toExpr r, 
      toExpr s ]

instance : ToExpr (Inductive k) where toExpr
  | .mk n l ty p i cs rs r s r' => 
    .mkList [
      toExpr n, 
      toExpr l, 
      toExpr ty, 
      toExpr p, 
      toExpr i, 
      toExpr cs, 
      toExpr rs, 
      toExpr r, 
      toExpr s, 
      toExpr r' ]

instance : ToExpr QuotKind where toExpr
  | .type => toExpr 0
  | .ctor => toExpr 1
  | .lift => toExpr 2
  | .ind  => toExpr 3

instance : ToExpr (Definition k) where toExpr
  | .mk n l ty v s => 
    .mkList [
      toExpr n, 
      toExpr l, 
      toExpr ty, 
      toExpr v, 
      toExpr s ]

def Univ.toLurk : Univ k → Lurk.Expr
  | .zero     => .mkList [.u64 $ UNIV k, .nat 0]
  | .succ p   => .mkList [.u64 $ UNIV k, .nat 1, toExpr p]
  | .max a b  => .mkList [.u64 $ UNIV k, .nat 2, toExpr a, toExpr b]
  | .imax a b => .mkList [.u64 $ UNIV k, .nat 3, toExpr a, toExpr b]
  | .var n    => .mkList [.u64 $ UNIV k, .nat 4, toExpr n]

def Expr.toLurk : Expr k → Lurk.Expr
  | .var n i ls    => .mkList [.u64 $ EXPR k, .nat 0, toExpr n, toExpr i, toExpr ls]
  | .sort u        => .mkList [.u64 $ EXPR k, .nat 1, toExpr u]
  | .const n c ls  => .mkList [.u64 $ EXPR k, .nat 2, toExpr n, toExpr c, toExpr ls]
  | .app f a       => .mkList [.u64 $ EXPR k, .nat 3, toExpr f, toExpr a]
  | .lam n i d b   => .mkList [.u64 $ EXPR k, .nat 4, toExpr n, toExpr i, toExpr d, toExpr b]
  | .pi n i d b    => .mkList [.u64 $ EXPR k, .nat 5, toExpr n, toExpr i, toExpr d, toExpr b]
  | .letE n ty v b => .mkList [.u64 $ EXPR k, .nat 6, toExpr n, toExpr ty, toExpr v, toExpr b]
  | .lit l         => .mkList [.u64 $ EXPR k, .nat 7, toExpr l]
  | .proj n e      => .mkList [.u64 $ EXPR k, .nat 8, toExpr n, toExpr e]

def Const.toLurk : Const k → Lurk.Expr
  | .axiom ⟨n, l, ty, s⟩                 => .mkList [.u64 $ CONST k, .nat 0, toExpr n, toExpr l, toExpr ty, toExpr s]
  | .theorem ⟨n, l, ty, v⟩               => .mkList [.u64 $ CONST k, .nat 1, toExpr n, toExpr l, toExpr ty, toExpr v]
  | .opaque ⟨n, l, ty, v, s⟩             => .mkList [.u64 $ CONST k, .nat 2, toExpr n, toExpr l, toExpr ty, toExpr v, toExpr s]
  | .quotient ⟨n, l, ty, K⟩              => .mkList [.u64 $ CONST k, .nat 3, toExpr n, toExpr l, toExpr ty, toExpr K]
  | .inductiveProj ⟨n, l, ty, b, i⟩      => .mkList [.u64 $ CONST k, .nat 5, toExpr n, toExpr l, toExpr ty, toExpr b, toExpr i]
  | .constructorProj ⟨n, l, ty, b, i, j⟩ => .mkList [.u64 $ CONST k, .nat 6, toExpr n, toExpr l, toExpr ty, toExpr b, toExpr i, toExpr j]
  | .recursorProj ⟨n, l, ty, b, i, j⟩    => .mkList [.u64 $ CONST k, .nat 7, toExpr n, toExpr l, toExpr ty, toExpr b, toExpr i, toExpr j]
  | .definitionProj ⟨n, l, ty, b, i⟩     => .mkList [.u64 $ CONST k, .nat 8, toExpr n, toExpr l, toExpr ty, toExpr b, toExpr i]
  | .mutDefBlock b                       => .mkList [.u64 $ CONST k, .nat 9, toExpr b]
  | .mutIndBlock b                       => .mkList [.u64 $ CONST k, .nat 10, toExpr b]

def Univ.toCid (univ : Univ k) : Lurk.Expr × UnivCid k :=
  let data := univ.toLurk
  (data, ⟨hash data⟩)

def Expr.toCid (expr : Expr k) : Lurk.Expr × ExprCid k :=
  let data := expr.toLurk
  (data, ⟨hash data⟩)

def Const.toCid (const : Const k) : Lurk.Expr × ConstCid k :=
  let data := const.toLurk
  (data, ⟨hash data⟩)

def LurkStore.toLurk.Expr (store : LurkStore) : Lurk.Expr :=
  .mkList [
    .u64 STORE,
    toExpr store.consts,
    toExpr store.univAnon,
    toExpr store.exprAnon,
    toExpr store.constAnon,
    toExpr store.univMeta,
    toExpr store.exprMeta,
    toExpr store.constMeta]

end IR

end Yatima
