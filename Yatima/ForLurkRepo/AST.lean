import Yatima.ForLurkRepo.SExpr
import Yatima.ForLurkRepo.PreUtils
import Lean

namespace Lurk

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- Binary operations on Lurk numerals -/
inductive BinaryOp | sum | diff | prod | quot | numEq | lt | gt | le | ge | eq
deriving Repr, BEq

/-- Basic Lurk primitives -/
inductive Literal
  -- `t` `nil`
  | t | nil
  -- Numerical values
  | num  : Fin N → Literal
  -- Strings
  | str  : String → Literal
  -- Characters
  | char : Char → Literal
  deriving Repr, BEq, Inhabited

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

def mkAppOrNoaryLam (f : Expr) : List Expr → Expr
  | a :: as => as.foldl (init := .app f a) fun acc a => .app acc a
  | [] => .lam [] f

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
