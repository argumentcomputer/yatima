import Ipld.Ipld
import Yatima.Datatypes.Const
import Yatima.Typechecker.Datatypes

namespace Yatima

namespace IR

open Std (RBMap RBSet) in
/-- The end result of the compilation process -/
structure Store where
  consts : RBSet (Both ConstCid) compare

  univAnon  : RBMap (UnivCid  .anon) (Univ  .anon) compare
  exprAnon  : RBMap (ExprCid  .anon) (Expr  .anon) compare
  constAnon : RBMap (ConstCid .anon) (Const .anon) compare

  univMeta  : RBMap (UnivCid  .meta) (Univ  .meta) compare
  exprMeta  : RBMap (ExprCid  .meta) (Expr  .meta) compare
  constMeta : RBMap (ConstCid .meta) (Const .meta) compare
  deriving Inhabited

instance : BEq Store where
  beq x y := x.consts.toList == y.consts.toList
    && x.univAnon.toList  == y.univAnon.toList
    && x.exprAnon.toList  == y.exprAnon.toList
    && x.constAnon.toList == y.constAnon.toList
    && x.univMeta.toList  == y.univMeta.toList
    && x.univMeta.toList  == y.univMeta.toList
    && x.constMeta.toList == y.constMeta.toList

def Store.union (s s' : Store) : Store := ⟨
  s'.consts.union s.consts,
  s'.univAnon.foldl  (init := s.univAnon)  fun acc cid x => acc.insert cid x,
  s'.exprAnon.foldl  (init := s.exprAnon)  fun acc cid x => acc.insert cid x,
  s'.constAnon.foldl (init := s.constAnon) fun acc cid x => acc.insert cid x,
  s'.univMeta.foldl  (init := s.univMeta)  fun acc cid x => acc.insert cid x,
  s'.exprMeta.foldl  (init := s.exprMeta)  fun acc cid x => acc.insert cid x,
  s'.constMeta.foldl (init := s.constMeta) fun acc cid x => acc.insert cid x
⟩

end IR

namespace TC

open Typechecker in
/-- Keeps track of the data used for typechecking -/
structure Store where
  consts       : Array Const
  primIdxs     : Std.RBMap PrimConst Nat compare
  idxsToPrims  : Std.RBMap Nat PrimConst compare
  deriving Inhabited

end TC

namespace Ipld

/-- Contains `IR.Store` data encoded in IPLD -/
structure Store where
  consts    : Array Ipld
  univAnon  : Array Ipld
  exprAnon  : Array Ipld
  constAnon : Array Ipld
  univMeta  : Array Ipld
  exprMeta  : Array Ipld
  constMeta : Array Ipld

end Ipld

end Yatima
