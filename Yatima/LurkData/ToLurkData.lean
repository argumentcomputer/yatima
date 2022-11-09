import Yatima.Datatypes.Store
import Yatima.Datatypes.Cid
import Yatima.LurkData.Move

open Lurk.Syntax AST ToAST

namespace Lurk.Syntax

instance : ToAST Bool where toAST
  | false => .nil
  | true  => .t

instance [ToAST α] [ToAST β] : ToAST (α ⊕ β) where toAST
  | .inl a => toAST a
  | .inr b => toAST b

instance [ToAST α] : ToAST (Option α) where toAST
  | none   => .nil
  | some a => toAST [a] -- Note we can't write `toAST a` here because `a` could be `nil`

end Lurk.Syntax

namespace Yatima.IR

def partitionName (name : Name) : List (String ⊕ Nat) :=
  let rec aux (acc : List (String ⊕ Nat)) : Name → List (String ⊕ Nat)
    | .str name s => aux ((.inl s) :: acc) name
    | .num name n => aux ((.inr n) :: acc) name
    | .anonymous  => acc
  aux [] name

instance : ToAST Name where
  toAST x :=
    let parts := (partitionName x).foldl (fun acc y =>acc.push (toAST y)) #[]
    consWith parts.data .nil

instance : ToAST (UnivCid  k) where toAST u := ~[.comm, .f u.data]
instance : ToAST (ExprCid  k) where toAST u := ~[.comm, .f u.data]
instance : ToAST (ConstCid k) where toAST u := ~[.comm, .f u.data]

instance : ToAST BinderInfo where toAST
  | .default        => toAST 0
  | .implicit       => toAST 1
  | .strictImplicit => toAST 2
  | .instImplicit   => toAST 3

instance : ToAST Literal where toAST
  | .natVal n => toAST n
  | .strVal s => toAST s

instance : ToAST DefinitionSafety where toAST
  | .safe    => toAST 0
  | .unsafe  => toAST 1
  | .partial => toAST 2

instance [ToAST α] [ToAST β] : ToAST (Split α β k) where toAST
  | .injₗ a => .cons (toAST 0) (toAST a)
  | .injᵣ b => .cons (toAST 1) (toAST b)

instance : ToAST Unit where toAST
  | .unit => .nil

instance : (k : Kind) → ToAST (RecursorRule k)
  | .anon => { toAST := fun | .mk c f r => ~[toAST c, toAST f, toAST r] }
  | .meta => { toAST := fun | .mk c f r => ~[toAST c, toAST f, toAST r] }

instance : ToAST (Recursor b k) where toAST
  | .mk n l ty p i m m' rs k =>
    ~[toAST n,
      toAST l,
      toAST ty,
      toAST p,
      toAST i,
      toAST m,
      toAST m',
      toAST rs,
      toAST k ]

instance : ToAST (Sigma (Recursor · k)) where toAST
  | .mk b (.mk n l ty p i m m' rs k) =>
    ~[toAST (b : Bool),
      toAST n,
      toAST l,
      toAST ty,
      toAST p,
      toAST i,
      toAST m,
      toAST m',
      toAST rs,
      toAST k ]

instance : ToAST (Constructor k) where toAST
  | .mk n ty l i p f r s =>
    ~[toAST n,
      toAST ty,
      toAST l,
      toAST i,
      toAST p,
      toAST f,
      toAST r,
      toAST s ]

instance : ToAST (Inductive k) where toAST
  | .mk n l ty p i cs rs r s r' =>
    ~[toAST n,
      toAST l,
      toAST ty,
      toAST p,
      toAST i,
      toAST cs,
      toAST rs,
      toAST r,
      toAST s,
      toAST r' ]

instance : ToAST QuotKind where toAST
  | .type => toAST 0
  | .ctor => toAST 1
  | .lift => toAST 2
  | .ind  => toAST 3

instance : ToAST (Definition k) where toAST
  | .mk n l ty v s =>
    ~[toAST n,
      toAST l,
      toAST ty,
      toAST v,
      toAST s ]

def Univ.toLurk : Univ k → Lurk.Syntax.AST
  | .zero     => ~[.u64 $ UNIV k, .num 0]
  | .succ p   => ~[.u64 $ UNIV k, .num 1, toAST p]
  | .max a b  => ~[.u64 $ UNIV k, .num 2, toAST a, toAST b]
  | .imax a b => ~[.u64 $ UNIV k, .num 3, toAST a, toAST b]
  | .var n    => ~[.u64 $ UNIV k, .num 4, toAST n]

def Expr.toLurk : Expr k → Lurk.Syntax.AST
  | .var n i ls    => ~[.u64 $ EXPR k, .num 0, toAST n, toAST i, toAST ls]
  | .sort u        => ~[.u64 $ EXPR k, .num 1, toAST u]
  | .const n c ls  => ~[.u64 $ EXPR k, .num 2, toAST n, toAST c, toAST ls]
  | .app f a       => ~[.u64 $ EXPR k, .num 3, toAST f, toAST a]
  | .lam n i d b   => ~[.u64 $ EXPR k, .num 4, toAST n, toAST i, toAST d, toAST b]
  | .pi n i d b    => ~[.u64 $ EXPR k, .num 5, toAST n, toAST i, toAST d, toAST b]
  | .letE n ty v b => ~[.u64 $ EXPR k, .num 6, toAST n, toAST ty, toAST v, toAST b]
  | .lit l         => ~[.u64 $ EXPR k, .num 7, toAST l]
  | .proj n e      => ~[.u64 $ EXPR k, .num 8, toAST n, toAST e]

def Const.toLurk : Const k → Lurk.Syntax.AST
  | .axiom ⟨n, l, ty, s⟩                 => ~[.u64 $ CONST k, .num 0, toAST n, toAST l, toAST ty, toAST s]
  | .theorem ⟨n, l, ty, v⟩               => ~[.u64 $ CONST k, .num 1, toAST n, toAST l, toAST ty, toAST v]
  | .opaque ⟨n, l, ty, v, s⟩             => ~[.u64 $ CONST k, .num 2, toAST n, toAST l, toAST ty, toAST v, toAST s]
  | .quotient ⟨n, l, ty, K⟩              => ~[.u64 $ CONST k, .num 3, toAST n, toAST l, toAST ty, toAST K]
  | .inductiveProj ⟨n, l, ty, b, i⟩      => ~[.u64 $ CONST k, .num 5, toAST n, toAST l, toAST ty, toAST b, toAST i]
  | .constructorProj ⟨n, l, ty, b, i, j⟩ => ~[.u64 $ CONST k, .num 6, toAST n, toAST l, toAST ty, toAST b, toAST i, toAST j]
  | .recursorProj ⟨n, l, ty, b, i, j⟩    => ~[.u64 $ CONST k, .num 7, toAST n, toAST l, toAST ty, toAST b, toAST i, toAST j]
  | .definitionProj ⟨n, l, ty, b, i⟩     => ~[.u64 $ CONST k, .num 8, toAST n, toAST l, toAST ty, toAST b, toAST i]
  | .mutDefBlock b                       => ~[.u64 $ CONST k, .num 9, toAST b]
  | .mutIndBlock b                       => ~[.u64 $ CONST k, .num 10, toAST b]

def Univ.toCid (univ : Univ k) : Lurk.Syntax.AST × UnivCid k :=
  let data := univ.toLurk
  (data, ⟨hash data⟩)

def Expr.toCid (expr : Expr k) : Lurk.Syntax.AST × ExprCid k :=
  let data := expr.toLurk
  (data, ⟨hash data⟩)

def Const.toCid (const : Const k) : Lurk.Syntax.AST × ConstCid k :=
  let data := const.toLurk
  (data, ⟨hash data⟩)

def LurkStore.toLurk.Syntax.AST (store : LurkStore) : Lurk.Syntax.AST :=
  ~[.u64 STORE,
    toAST store.consts,
    toAST store.univAnon,
    toAST store.exprAnon,
    toAST store.constAnon,
    toAST store.univMeta,
    toAST store.exprMeta,
    toAST store.constMeta]

end Yatima.IR
