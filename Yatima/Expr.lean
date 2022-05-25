import Yatima.Univ

namespace Yatima

inductive LitType
  | nat : LitType
  | str : LitType
  deriving BEq, Inhabited

inductive Literal
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Inhabited

inductive BinderInfo
  | default
  | implicit
  | strictImplicit
  | instImplicit
  | auxDecl
  deriving BEq, Inhabited

inductive Expr
  | var   : Name → Nat → Expr
  | sort  : UnivCid → Expr
  | const : Name → ConstCid → List UnivCid → Expr
  | app   : ExprCid → ExprCid → Expr
  | lam   : Name → BinderInfo → ExprCid → ExprCid → Expr
  | pi    : Name → BinderInfo → ExprCid → ExprCid → Expr
  | letE  : Name → ExprCid → ExprCid → ExprCid → Expr
  | lit   : Literal → Expr
  | lty   : LitType → Expr
  | fix   : Name → ExprCid → Expr
  deriving BEq, Inhabited

inductive ExprAnon
  | var   : Nat → ExprAnon
  | sort  : UnivAnonCid → ExprAnon
  | const : ConstAnonCid → List UnivAnonCid → ExprAnon
  | app   : ExprAnonCid → ExprAnonCid → ExprAnon
  | lam   : ExprAnonCid → ExprAnonCid → ExprAnon
  | pi    : ExprAnonCid → ExprAnonCid → ExprAnon
  | letE  : ExprAnonCid → ExprAnonCid → ExprAnonCid → ExprAnon
  | lit   : Literal → ExprAnon
  | lty   : LitType → ExprAnon
  | fix   : ExprAnonCid → ExprAnon
  deriving BEq, Inhabited

inductive ExprMeta
  | var   : Name → ExprMeta
  | sort  : UnivMetaCid → ExprMeta
  | const : Name → ConstMetaCid → List UnivMetaCid → ExprMeta
  | app   : ExprMetaCid → ExprMetaCid → ExprMeta
  | lam   : Name → BinderInfo → ExprMetaCid → ExprMetaCid → ExprMeta
  | pi    : Name → BinderInfo → ExprMetaCid → ExprMetaCid → ExprMeta
  | letE  : ExprMetaCid → ExprMetaCid → ExprMetaCid → ExprMeta
  | lit   : Literal → ExprMeta
  | lty   : LitType → ExprMeta
  | fix   : Name → ExprMetaCid → ExprMeta
  deriving BEq, Inhabited

def Expr.toAnon : Expr → ExprAnon
  | var _ n         => .var n
  | sort u          => .sort u.anon
  | const _ c us    => .const c.anon $ us.map (·.anon)
  | app e e'        => .app e.anon e'.anon
  | lam _ _ e e'    => .lam e.anon e'.anon
  | pi _ _ e e'     => .lam e.anon e'.anon
  | letE _ e e' e'' => .letE e.anon e'.anon e''.anon
  | lit l           => .lit l
  | lty l           => .lty l
  | fix _ e         => .fix e.anon

def Expr.toMeta : Expr → ExprMeta
  | var n _         => .var n
  | sort u          => .sort u.meta
  | const n c us    => .const n c.meta $ us.map (·.meta)
  | app e e'        => .app e.meta e'.meta
  | lam n b e e'    => .lam n b e.meta e'.meta
  | pi n b e e'     => .pi n b e.meta e'.meta
  | letE _ e e' e'' => .letE e.meta e'.meta e''.meta
  | lit l           => .lit l
  | lty l           => .lty l
  | fix n e         => .fix n e.meta

end Yatima
