import Yatima.ForLurkRepo.SExpr
import Yatima.ForLurkRepo.PreUtils
import Yatima.ForLurkRepo.FixName
import Lean

namespace Lurk

/-- Binary operations on Lurk numerals -/
inductive BinaryOp | sum | diff | prod | quot | numEq | lt | gt | le | ge | eq
deriving Repr, BEq

/-- Basic Lurk expression AST -/
inductive Expr where
  -- `t`, `nil`, numeric, string and char literals
  | lit      : Literal → Expr
  -- Symbols to reference content in the environment
  | sym      : Name → Expr
  -- `if <test> <consequent> <alternate>`
  | ifE      : Expr → Expr → Expr → Expr
  -- `lambda <formals> <body>`
  | lam      : List Name → Expr → Expr
  -- `let <bindings> <body>`
  | letE     : List (Name × Expr) → Expr → Expr
  -- `letrec <bindings> <body>`
  | letRecE  : List (Name × Expr) → Expr → Expr
  -- `mutrec <bindings> <body>`
  | mutRecE  : List (Name × Expr) → Expr → Expr
  -- `<fun>`
  | app₀     : Expr → Expr
  -- `<fun> <arg>`
  | app      : Expr → Expr → Expr
  -- `quote <datum>`
  | quote    : SExpr → Expr
  -- `<binop> <e1> <e2>`
  | binaryOp : BinaryOp → Expr → Expr → Expr
  -- `<cons> <e1> <e2>`
  | cons : Expr → Expr → Expr
  -- `<strcons> <e1> <e2>`
  | strcons  : Expr → Expr → Expr
  -- `atom <e>`
  | atom     : Expr → Expr
  -- `car <e>`
  | car      : Expr → Expr
  -- `cdr <e>`
  | cdr      : Expr → Expr
  -- `emit <e>`
  | emit     : Expr → Expr
  -- `begin <e1> <e2> ...`
  | begin    : List Expr → Expr
  -- `current-env`
  | currEnv  : Expr
  deriving Repr, BEq, Inhabited

namespace Expr

def mkApp (f : Expr) : List Expr → Expr
  | a :: as => as.foldl (init := .app f a) fun acc a => .app acc a
  | [] => .app₀ f

def mkListWith (es : List Expr) (tail : Expr) : Expr := 
  es.foldr (init := tail)
    fun n acc => .cons n acc

def mkList (es : List Expr) : Expr :=   
  mkListWith es (.lit .nil)

/--
Remove all binders from an expression, converting a lambda into
an "implicit lambda". This is useful for constructing the `rhs` of
recursor rules.
-/
def toImplicitLambda : Expr → Expr
  | .lam _ body => toImplicitLambda body
  | x => x

class ToExpr (α : Type u) where 
  toExpr : α → Expr 

instance : ToExpr Nat where 
  toExpr n := .lit $ .num (Fin.ofNat n)
  
instance : ToExpr Int where 
  toExpr n := .lit $ .num (Fin.ofInt n)

instance : ToExpr (Fin N) where 
  toExpr n := .lit $ .num n

instance : ToExpr Name where 
  toExpr := .sym

/-- Non-instance version when we want lurk-friendly names -/
def toExprFix (n : Name) : Expr := 
  .sym (fixName n false)

instance : ToExpr String where 
  toExpr s := .lit $ .str s

instance : ToExpr Char where 
  toExpr c := .lit $ .char c

instance : ToExpr Expr where 
  toExpr s := s
