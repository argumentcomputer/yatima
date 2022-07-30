import Yatima.ForLurkRepo.SExpr

namespace Lurk

/-- Unary operations on Lurk expressions -/
inductive UnaryOp | car | cdr | atom | emit
deriving Repr, BEq

/-- Binary operations on Lurk numerals -/
inductive BinOp | cons | strcons | sum | diff | prod | quot | eq | nEq
deriving Repr, BEq

/-- Basic Lurk primitives -/
inductive Literal
  -- `t` `nil`
  | t | nil
  -- Numerical values
  | num     : Int → Literal
  -- Strings
  | str     : String → Literal
  -- Characters
  | char    : Char → Literal
  -- Symbols
  | sym     : String → Literal
  deriving Repr

/-- Basic Lurk expression AST -/
inductive Expr where
  -- `t`, `nil`, numeric, string and char literals
  | lit   : Literal → Expr
  -- `if <test> <consequent> <alternate>`
  | ifE     : Expr → Expr → Expr → Expr
  -- `lambda <formals> <body>`
  | lam     : List String → Expr → Expr
  -- `let <bindings> <body>`
  | letE    : List (String × Expr) → Expr → Expr
  -- `letrec <bindings> <body>`
  | letRecE : List (String × Expr) → Expr → Expr
  -- `<fun> <args>`
  | app     : Expr → List Expr → Expr 
  -- `quote <datum>`
  | quote   : SExpr → Expr
  -- `<unaryop> <e>`
  | unaryOp : UnaryOp → Expr → Expr
  -- `<binop> <e1> <e2>`
  | binOp   : BinOp → Expr → Expr → Expr    
  -- `emit <e>`
  | emit    : Expr → Expr
  -- `begin <e1> <e2> ... `
  | begin   : List Expr → Expr
  -- `current-env`
  | currEnv : Expr
  -- `eval <expr> <env>`
  | eval    : Expr → Option Expr → Expr
  deriving Repr

namespace Expr 

class ToExpr (α : Type u) where 
  toExpr : α → Expr 

instance : ToExpr Nat where 
  toExpr n := .lit $ .num n
  
instance : ToExpr Int where 
  toExpr n := .lit $ .num n

instance : ToExpr String where 
  toExpr s := .lit $ .str s

instance : ToExpr Char where 
  toExpr c := .lit $ .char c

instance : ToExpr Expr where 
  toExpr s := s