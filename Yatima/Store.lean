import Yatima.Expr

namespace Yatima

open Std (RBMap) in
structure Store where
  univ_cache  : RBMap UnivCid Univ compare
  expr_cache  : RBMap ExprCid Expr compare
  const_cache : RBMap ConstCid Const compare

  univ_anon  : RBMap (Ipld.UnivCid .Anon) (Ipld.Univ .Anon)  compare
  expr_anon  : RBMap (Ipld.ExprCid .Anon) (Ipld.Expr .Anon)  compare
  const_anon : RBMap (Ipld.ConstCid .Anon) (Ipld.Const .Anon) compare

  univ_meta  : RBMap (Ipld.UnivCid .Meta) (Ipld.Univ .Meta)  compare
  expr_meta  : RBMap (Ipld.ExprCid .Meta) (Ipld.Expr .Meta)  compare
  const_meta : RBMap (Ipld.ConstCid .Meta) (Ipld.Const .Meta) compare

instance : Inhabited Store where
  default := ⟨
    .empty, .empty, .empty,
    .empty, .empty, .empty,
    .empty, .empty, .empty
  ⟩

def Store.union (s s' : Store) : Store := ⟨
  s'.univ_cache.fold  (init := s.univ_cache)  fun acc cid x => acc.insert cid x,
  s'.expr_cache.fold  (init := s.expr_cache)  fun acc cid x => acc.insert cid x,
  s'.const_cache.fold (init := s.const_cache) fun acc cid x => acc.insert cid x,
  s'.univ_anon.fold   (init := s.univ_anon)   fun acc cid x => acc.insert cid x,
  s'.expr_anon.fold   (init := s.expr_anon)   fun acc cid x => acc.insert cid x,
  s'.const_anon.fold  (init := s.const_anon)  fun acc cid x => acc.insert cid x,
  s'.univ_meta.fold   (init := s.univ_meta)   fun acc cid x => acc.insert cid x,
  s'.expr_meta.fold   (init := s.expr_meta)   fun acc cid x => acc.insert cid x,
  s'.const_meta.fold  (init := s.const_meta)  fun acc cid x => acc.insert cid x
⟩

inductive Store.Entry
  | univ_cache  : UnivCid × Univ                             → Store.Entry
  | expr_cache  : ExprCid × Expr                             → Store.Entry
  | const_cache : ConstCid × Const                           → Store.Entry
  | univ_anon   : (Ipld.UnivCid .Anon) × (Ipld.Univ .Anon)   → Store.Entry
  | expr_anon   : (Ipld.ExprCid .Anon) × (Ipld.Expr .Anon)   → Store.Entry
  | const_anon  : (Ipld.ConstCid .Anon) × (Ipld.Const .Anon) → Store.Entry
  | univ_meta   : (Ipld.UnivCid .Meta) × (Ipld.Univ .Meta)   → Store.Entry
  | expr_meta   : (Ipld.ExprCid .Meta) × (Ipld.Expr .Meta)   → Store.Entry
  | const_meta  : (Ipld.ConstCid .Meta) × (Ipld.Const .Meta) → Store.Entry

inductive Store.Key : Type → Type
  | univ_cache  : UnivCid             → Store.Key Univ
  | expr_cache  : ExprCid             → Store.Key Expr
  | const_cache : ConstCid            → Store.Key Const
  | univ_anon   : Ipld.UnivCid .Anon  → Store.Key (Ipld.Univ .Anon)
  | expr_anon   : Ipld.ExprCid .Anon  → Store.Key (Ipld.Expr .Anon)
  | const_anon  : Ipld.ConstCid .Anon → Store.Key (Ipld.Const .Anon)
  | univ_meta   : Ipld.UnivCid .Meta  → Store.Key (Ipld.Univ .Meta)
  | expr_meta   : Ipld.ExprCid .Meta  → Store.Key (Ipld.Expr .Meta)
  | const_meta  : Ipld.ConstCid .Meta → Store.Key (Ipld.Const .Meta)

instance : Coe (UnivCid × Univ) Store.Entry where coe := .univ_cache
instance : Coe (ExprCid × Expr) Store.Entry where coe := .expr_cache
instance : Coe (ConstCid × Const) Store.Entry where coe := .const_cache
instance : Coe ((Ipld.UnivCid .Anon) × (Ipld.Univ .Anon)) Store.Entry where coe := .univ_anon
instance : Coe ((Ipld.ExprCid .Anon) × (Ipld.Expr .Anon)) Store.Entry where coe := .expr_anon
instance : Coe ((Ipld.ConstCid .Anon) × (Ipld.Const .Anon)) Store.Entry where coe := .const_anon
instance : Coe ((Ipld.UnivCid .Meta) × (Ipld.Univ .Meta)) Store.Entry where coe := .univ_meta
instance : Coe ((Ipld.ExprCid .Meta) × (Ipld.Expr .Meta)) Store.Entry where coe := .expr_meta
instance : Coe ((Ipld.ConstCid .Meta) × (Ipld.Const .Meta)) Store.Entry where coe := .const_meta

end Yatima
