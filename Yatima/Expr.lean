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

namespace Expr

def shift (inc : Nat) (dep : Option Nat) : Expr → Expr
  | var name idx                => match dep with
    | some dep => if idx < dep then var name idx else var name <| idx + inc
    | none     => var name <| idx + inc
  | sort lvl                    => sort lvl
  | const name cid lvls         => const name cid lvls
  | app func input              => app (func.shift inc dep) (input.shift inc dep)
  | lam name bind type body     => lam name bind (type.shift inc dep) (body.shift inc dep)
  | pi name bind type body      => pi name bind (type.shift inc dep) (body.shift inc dep)
  | letE name expr1 expr2 expr3 =>  letE name (expr1.shift inc dep) (expr2.shift inc dep) (expr3.shift    inc dep)
  | lit litr                    => lit litr
  | lty litType                 => lty litType
  | fix name expr               => fix name <| expr.shift inc dep

end Expr

end Yatima

namespace tests


end tests

