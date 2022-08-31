import Yatima.ForLurkRepo.SExpr
import Yatima.ForLurkRepo.PreUtils

namespace Lurk

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- Unary operations on Lurk expressions -/
inductive UnaryOp | car | cdr | atom | emit
deriving Repr, BEq

/-- Binary operations on Lurk numerals -/
inductive BinaryOp | cons | strcons | sum | diff | prod | quot | eq | nEq
deriving Repr, BEq

/-- Basic Lurk primitives -/
inductive Literal
  -- `t` `nil`
  | t | nil
  -- Numerical values
  | num     : Fin N → Literal
  -- Strings
  | str     : String → Literal
  -- Characters
  | char    : Char → Literal
  -- Symbols
  | sym     : Name → Literal
  deriving Repr, BEq, Inhabited

/-- Basic Lurk expression AST -/
inductive Expr where
  -- `t`, `nil`, numeric, string and char literals
  | lit   : Literal → Expr
  -- `if <test> <consequent> <alternate>`
  | ifE     : Expr → Expr → Expr → Expr
  -- `lambda <formals> <body>`
  | lam     : List Name → Expr → Expr
  -- `let <bindings> <body>`
  | letE    : List (Name × Expr) → Expr → Expr
  -- `letrec <bindings> <body>`
  | letRecE : List (Name × Expr) → Expr → Expr
  -- `<fun> <args>`
  | app     : Expr → List Expr → Expr 
  -- `quote <datum>`
  | quote   : SExpr → Expr
  -- `<unaryop> <e>`
  | unaryOp : UnaryOp → Expr → Expr
  -- `<binop> <e1> <e2>`
  | binaryOp   : BinaryOp → Expr → Expr → Expr    
  -- `emit <e>`
  | emit    : Expr → Expr
  -- `begin <e1> <e2> ...`
  | begin   : List Expr → Expr
  -- `current-env`
  | currEnv : Expr
  -- `eval <expr> <env>`
  | eval    : Expr → Option Expr → Expr
  deriving Repr, BEq, Inhabited

namespace Expr

class ToExpr (α : Type u) where 
  toExpr : α → Expr 

instance : ToExpr Nat where 
  toExpr n := .lit $ .num (Fin.ofNat n)
  
instance : ToExpr Int where 
  toExpr n := .lit $ .num (Fin.ofInt n)

instance : ToExpr (Fin N) where 
  toExpr n := .lit $ .num n

instance : ToExpr Name where 
  toExpr s := .lit $ .sym s

/-- Non-instance version when we want lurk-friendly names -/
def toExprFix (n : Name) : Expr := 
  .lit $ .sym (fixName n false)

instance : ToExpr String where 
  toExpr s := .lit $ .str s

instance : ToExpr Char where 
  toExpr c := .lit $ .char c

instance : ToExpr Expr where 
  toExpr s := s