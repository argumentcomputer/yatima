import Yatima.Env
import Yatima.Univ

namespace Yatima

  inductive Bind
  | default
  | implicit
  | strictImplicit
  | instImplicit
  deriving BEq, Inhabited

  inductive LitType
  | nat : LitType
  | str : LitType
  deriving BEq, Inhabited

  inductive Literal
  | nat : Nat → Literal
  | str : String → Literal
  deriving BEq, Inhabited

  inductive Expr
  | var   : Name → Nat → Expr
  | sort  : Univ → Expr
  | const : Name → ConstCid → List Univ → Expr
  | app   : Expr → Expr → Expr
  | lam   : Name → Bind → Expr → Expr → Expr
  | pi    : Name → Bind → Expr → Expr → Expr
  | letE  : Name → Expr → Expr → Expr → Expr
  | lit   : Literal → Expr
  | lty   : LitType → Expr
  | fix   : Name → Expr → Expr
  deriving BEq, Inhabited

  inductive ExprAnon
  | var   : Nat → ExprAnon
  | sort  : UnivAnonCid → ExprAnon
  | const : ConstAnonCid → List UnivAnonCid → ExprAnon
  | app   : ExprAnonCid → ExprAnonCid → ExprAnon
  | lam   : Bind → ExprAnonCid → ExprAnonCid → ExprAnon
  | pi    : Bind → ExprAnonCid → ExprAnonCid → ExprAnon
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
  | lam   : Name → ExprMetaCid → ExprMetaCid → ExprMeta
  | pi    : Name → ExprMetaCid → ExprMetaCid → ExprMeta
  | letE  : ExprMetaCid → ExprMetaCid → ExprMetaCid → ExprMeta
  | lit   : ExprMeta
  | lty   : ExprMeta
  | fix   : Name → ExprMetaCid → ExprMeta
  deriving BEq, Inhabited

end Yatima
