import Yatima.Datatypes.Const
import Yatima.Typechecker.Datatypes
import Lurk.Syntax.AST
import Std.Data.RBMap.Basic

namespace Yatima

namespace IR

open Std (RBMap RBSet) in
/-- The end result of the compilation process -/
structure Store where
  consts : RBSet (Both ConstScalar) compare

  univAnon  : RBMap (UnivScalar  .anon) (Univ  .anon) compare
  exprAnon  : RBMap (ExprScalar  .anon) (Expr  .anon) compare
  constAnon : RBMap (ConstScalar .anon) (Const .anon) compare

  univMeta  : RBMap (UnivScalar  .meta) (Univ  .meta) compare
  exprMeta  : RBMap (ExprScalar  .meta) (Expr  .meta) compare
  constMeta : RBMap (ConstScalar .meta) (Const .meta) compare
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
  consts      : Array Const
  primIdxs    : Std.RBMap PrimConst Nat compare
  idxsToPrims : Std.RBMap Nat PrimConst compare
  deriving Inhabited

end TC

/-- Contains `IR.Store` data encoded in `Lurk.Syntax.AST` -/
structure Lurk.Store where
  consts    : Array Lurk.Syntax.AST
  univAnon  : Array Lurk.Syntax.AST
  exprAnon  : Array Lurk.Syntax.AST
  constAnon : Array Lurk.Syntax.AST
  univMeta  : Array Lurk.Syntax.AST
  exprMeta  : Array Lurk.Syntax.AST
  constMeta : Array Lurk.Syntax.AST

end Yatima
