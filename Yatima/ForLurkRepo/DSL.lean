import Lean
import Yatima.ForLurkRepo.Printing
import Yatima.ForLurkRepo.Utils

open Lean Elab Meta Term

declare_syntax_cat    lurk_literal
syntax "t"          : lurk_literal
syntax "nil"        : lurk_literal
syntax "-" noWs num : lurk_literal
syntax num          : lurk_literal
syntax str          : lurk_literal
syntax char         : lurk_literal
syntax ident        : lurk_literal

def elabLurkLiteral : Syntax → TermElabM Expr
  | `(lurk_literal| t)   => return mkConst ``Lurk.Literal.t
  | `(lurk_literal| nil) => return mkConst ``Lurk.Literal.nil
  | `(lurk_literal| -$n) => match n.getNat with
    | 0     => do
      mkAppM ``Lurk.Literal.num #[← mkAppM ``Int.ofNat #[mkConst ``Nat.zero]]
    | n + 1 => do
      mkAppM ``Lurk.Literal.num #[← mkAppM ``Int.negSucc #[mkNatLit n]]
  | `(lurk_literal| $n:num) => do
    mkAppM ``Lurk.Literal.num #[← mkAppM ``Int.ofNat #[mkNatLit n.getNat]]
  | `(lurk_literal| $s:str) =>
    mkAppM ``Lurk.Literal.str #[mkStrLit s.getString]
  | `(lurk_literal| $c:char) => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``Lurk.Literal.char #[c]
  | `(lurk_literal| $i:ident) =>
    mkAppM ``Lurk.Literal.sym #[mkStrLit i.getId.toString]
  | _ => throwUnsupportedSyntax

declare_syntax_cat  lurk_bin_op
syntax "cons "    : lurk_bin_op 
syntax "strcons " : lurk_bin_op
syntax "+ "       : lurk_bin_op
syntax "- "       : lurk_bin_op
syntax "* "       : lurk_bin_op
syntax "/ "       : lurk_bin_op
syntax "= "       : lurk_bin_op
syntax "eq "      : lurk_bin_op

def elabLurkBinOp : Syntax → TermElabM Expr
  | `(lurk_bin_op| cons) => return mkConst ``Lurk.BinOp.cons
  | `(lurk_bin_op| +)    => return mkConst ``Lurk.BinOp.sum
  | `(lurk_bin_op| -)    => return mkConst ``Lurk.BinOp.diff
  | `(lurk_bin_op| *)    => return mkConst ``Lurk.BinOp.prod
  | `(lurk_bin_op| /)    => return mkConst ``Lurk.BinOp.quot
  | `(lurk_bin_op| =)    => return mkConst ``Lurk.BinOp.eq
  | `(lurk_bin_op| eq)   => return mkConst ``Lurk.BinOp.nEq -- unfortunate clash again
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_unary_op 
syntax "car "  : lurk_unary_op
syntax "cdr "  : lurk_unary_op
syntax "atom " : lurk_unary_op
syntax "emit " : lurk_unary_op

def elabLurkUnaryOp : Syntax → TermElabM Expr
  | `(lurk_unary_op| car) => return mkConst ``Lurk.UnaryOp.car
  | `(lurk_unary_op| cdr) => return mkConst ``Lurk.UnaryOp.cdr
  | `(lurk_unary_op| atom) => return mkConst ``Lurk.UnaryOp.atom
  | `(lurk_unary_op| emit) => return mkConst ``Lurk.UnaryOp.emit
  | _ => throwUnsupportedSyntax

declare_syntax_cat           sexpr
syntax "-" noWs num        : sexpr
syntax num                 : sexpr
syntax ident               : sexpr
syntax str                 : sexpr
syntax char                : sexpr
syntax "(" sexpr+ ")"      : sexpr
syntax sexpr " . " sexpr   : sexpr
syntax "+"                 : sexpr
syntax "-"                 : sexpr
syntax "*"                 : sexpr
syntax "/"                 : sexpr
syntax "="                 : sexpr

partial def antiquoteToSExpr (e : Expr) : TermElabM Expr := do
  let e ← whnf e
  let type ← inferType e
  if ← isDefEq type (mkConst ``Nat) then 
    mkAppM ``Lurk.SExpr.num #[← mkAppM ``Int.ofNat #[e]]
  else if ← isDefEq type (mkConst ``Int) then 
    mkAppM ``Lurk.SExpr.num #[e]
  else if ← isDefEq type (mkConst ``String) then
    mkAppM ``Lurk.SExpr.str #[e]
  else if ← isDefEq type.getAppFn (Lean.mkConst ``List [levelZero]) then 
    let es := Expr.toListExpr e
    let es ← es.mapM antiquoteToSExpr
    mkAppM ``Lurk.SExpr.list #[← mkListLit (mkConst ``Lurk.SExpr) es]
  else if ← isDefEq type (mkConst ``Lurk.SExpr) then 
    return e
  else 
    throwUnsupportedSyntax

partial def elabSExpr : Syntax → TermElabM Expr
  | `(sexpr| -$n:num) => match n.getNat with
    | 0     => do
      mkAppM ``Lurk.SExpr.num #[← mkAppM ``Int.ofNat #[mkConst ``Nat.zero]]
    | n + 1 => do
      mkAppM ``Lurk.SExpr.num #[← mkAppM ``Int.negSucc #[mkNatLit n]]
  | `(sexpr| $n:num) => do
    mkAppM ``Lurk.SExpr.num #[← mkAppM ``Int.ofNat #[mkNatLit n.getNat]]
  | `(sexpr| $i:ident) => mkAppM ``Lurk.SExpr.atom #[mkStrLit i.getId.toString]
  | `(sexpr| +) => mkAppM ``Lurk.SExpr.atom #[mkStrLit "+"]
  | `(sexpr| -) => mkAppM ``Lurk.SExpr.atom #[mkStrLit "-"]
  | `(sexpr| *) => mkAppM ``Lurk.SExpr.atom #[mkStrLit "*"]
  | `(sexpr| /) => mkAppM ``Lurk.SExpr.atom #[mkStrLit "/"]
  | `(sexpr| =) => mkAppM ``Lurk.SExpr.atom #[mkStrLit "/"]
  | `(sexpr| $s:str) => mkAppM ``Lurk.SExpr.str #[mkStrLit s.getString]
  | `(sexpr| $c:char)  => do
    mkAppM ``Lurk.SExpr.char
      #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(sexpr| ($es*)) => do
    let es ← (es.mapM fun e => elabSExpr e)
    mkAppM ``Lurk.SExpr.list #[← mkListLit (mkConst ``Lurk.SExpr) es.toList]
  | `(sexpr| $e1 . $e2) => do
    mkAppM ``Lurk.SExpr.cons #[← elabSExpr e1, ← elabSExpr e2]
  | `(sexpr| $i) => do 
    if i.raw.isAntiquot then 
      let stx := i.raw.getAntiquotTerm
      let e ← elabTerm stx none
      antiquoteToSExpr e
    else 
      throwUnsupportedSyntax 
  | _ => throwUnsupportedSyntax

elab "[SExpr| " e:sexpr "]" : term =>
  elabSExpr e

declare_syntax_cat lurk_expr
declare_syntax_cat lurk_binding
declare_syntax_cat lurk_bindings

syntax "(" ident lurk_expr ")" : lurk_binding
syntax  "(" lurk_binding* ")"  : lurk_bindings

syntax lurk_literal                               : lurk_expr
syntax "(" "if" lurk_expr lurk_expr lurk_expr ")" : lurk_expr
syntax "(" "lambda" "(" ident* ")" lurk_expr ")"  : lurk_expr
syntax "(" "let" lurk_bindings lurk_expr ")"      : lurk_expr
syntax "(" "letrec" lurk_bindings lurk_expr ")"   : lurk_expr
syntax "(" "quote " sexpr ")"                     : lurk_expr
syntax "," sexpr                                  : lurk_expr
syntax "(" lurk_unary_op lurk_expr ")"            : lurk_expr
syntax "(" lurk_bin_op lurk_expr lurk_expr ")"    : lurk_expr
syntax "(" "emit" lurk_expr ")"                   : lurk_expr
syntax "(" "begin" lurk_expr*  ")"                : lurk_expr
syntax "current-env"                              : lurk_expr
syntax "(" "eval" lurk_expr  ")"                  : lurk_expr
syntax "(" lurk_expr* ")"                         : lurk_expr

partial def antiquoteToLurkExpr (e : Expr) : TermElabM Expr := do
  let e ← whnf e
  let type ← inferType e
  if ← isDefEq type (mkConst ``Nat) then 
    let lit ← mkAppM ``Lurk.Literal.num #[← mkAppM ``Int.ofNat #[e]]
    mkAppM ``Lurk.Expr.lit #[lit]
  else if ← isDefEq type (mkConst ``Int) then 
    let lit ← mkAppM ``Lurk.Literal.num #[e]
    mkAppM ``Lurk.Expr.lit #[lit]
  else if ← isDefEq type (mkConst ``String) then
    let lit ← mkAppM ``Lurk.Literal.str #[e]
    mkAppM ``Lurk.Expr.lit #[lit]
  else if ← isDefEq type (mkConst ``Lurk.Expr) then 
    return e
  else 
    throwUnsupportedSyntax

#check Lean.mkConst

/-- 
There are no type guarentees. 
-/
partial def elabLurkIdents (i : TSyntax `ident) : TermElabM $ Array Expr := do 
  if i.raw.isAntiquot then 
    let stx := i.raw.getAntiquotTerm
    let e ← elabTerm stx none
    let e ← whnf e
    let type ← inferType e
    match type.getAppFn with 
    | .const ``List _ _ => 
      let es := Expr.toListExpr e 
      return ⟨es⟩
    | _ => return ⟨[e]⟩
  else 
    return #[mkStrLit i.getId.toString] 

mutual 
partial def elabLurkBinding : Syntax → TermElabM Expr 
  | `(lurk_binding| ($name $body)) => do
    mkAppM ``Prod.mk #[mkStrLit name.getId.toString, ← elabLurkExpr body]
  | _ => throwUnsupportedSyntax

partial def elabLurkBindings : Syntax → TermElabM Expr 
  | `(lurk_bindings| ($bindings*)) => do 
    let bindings ← bindings.mapM elabLurkBinding
    let type ← mkAppM ``Prod #[mkConst ``String, mkConst ``Lurk.Expr]
    mkListLit type bindings.toList
  | _ => throwUnsupportedSyntax

partial def elabLurkExpr : TSyntax `lurk_expr → TermElabM Expr
  | `(lurk_expr| $l:lurk_literal) => do
    mkAppM ``Lurk.Expr.lit #[← elabLurkLiteral l]
  | `(lurk_expr| (if $test $con $alt)) => do
    mkAppM ``Lurk.Expr.ifE
      #[← elabLurkExpr test, ← elabLurkExpr con, ← elabLurkExpr alt]
  | `(lurk_expr| (lambda ($formals*) $body)) => do
    let formals ← formals.mapM elabLurkIdents
    let formals ← mkListLit (mkConst ``String) formals.concat.toList
    mkAppM ``Lurk.Expr.lam #[formals, ← elabLurkExpr body]
  | `(lurk_expr| (let $bind $body)) => do
    mkAppM ``Lurk.Expr.letE #[← elabLurkBindings bind, ← elabLurkExpr body]
  | `(lurk_expr| (letrec $bind $body)) => do
    mkAppM ``Lurk.Expr.letRecE #[← elabLurkBindings bind, ← elabLurkExpr body]
  | `(lurk_expr| (quote $datum)) => do
    mkAppM ``Lurk.Expr.quote #[← elabSExpr datum]
  | `(lurk_expr| ,$datum) => do
    mkAppM ``Lurk.Expr.quote #[← elabSExpr datum]
  | `(lurk_expr| ($op:lurk_unary_op $e)) => do
    mkAppM ``Lurk.Expr.unaryOp #[← elabLurkUnaryOp op, ← elabLurkExpr e]
  | `(lurk_expr| ($op:lurk_bin_op $e1 $e2)) => do
    mkAppM ``Lurk.Expr.binOp
      #[← elabLurkBinOp op, ← elabLurkExpr e1, ← elabLurkExpr e2]
  | `(lurk_expr| (emit $e)) => do
    mkAppM ``Lurk.Expr.emit #[← elabLurkExpr e]
  | `(lurk_expr| (begin $es*)) => do
    let es := (← es.mapM elabLurkExpr).toList
    let type := Lean.mkConst ``Lurk.Expr
    mkAppM ``Lurk.Expr.begin #[← mkListLit type es]
  | `(lurk_expr| current-env) => return mkConst ``Lurk.Expr.currEnv
  | `(lurk_expr| (eval $e)) => elabLurkExpr e
  | `(lurk_expr| ($e*)) => do
    let e := (← e.mapM elabLurkExpr).toList
    match e with 
    | []   => 
      let s ← mkAppM ``Lurk.Literal.sym #[mkStrLit "()"]
      mkAppM ``Lurk.Expr.lit #[s]
    | e::es => 
      let type := Lean.mkConst ``Lurk.Expr
      mkAppM ``Lurk.Expr.app #[e, ← mkListLit type es]
  | `(lurk_expr| $i) => do 
    if i.raw.isAntiquot then 
      let stx := i.raw.getAntiquotTerm
      let e ← elabTerm stx none
      antiquoteToLurkExpr e
    else 
      throwUnsupportedSyntax 
  | _ => throwUnsupportedSyntax
end

-- Tests 

elab "test_elabLurkLiteral " v:lurk_literal : term =>
  elabLurkLiteral v

#eval test_elabLurkLiteral 5     -- Lurk.Literal.num { data := 5, modulus? := none }
#eval test_elabLurkLiteral 0     -- Lurk.Literal.num { data := 0, modulus? := none }
#eval test_elabLurkLiteral -0    -- Lurk.Literal.num { data := 0, modulus? := none }
#eval test_elabLurkLiteral -5    -- Lurk.Literal.num { data := -5, modulus? := none }
#eval test_elabLurkLiteral ""    -- Lurk.Literal.str ""
#eval test_elabLurkLiteral "sss" -- Lurk.Literal.str "sss"
#eval test_elabLurkLiteral a     -- Lurk.Literal.sym { data := "a" }

elab "test_elabLurkBinOp " v:lurk_bin_op : term =>
  elabLurkBinOp v

#eval test_elabLurkBinOp +
#eval test_elabLurkBinOp -
#eval test_elabLurkBinOp *
#eval test_elabLurkBinOp /

elab "test_elabLurkUnaryOp " v:lurk_unary_op : term =>
  elabLurkUnaryOp v

#eval test_elabLurkUnaryOp car

elab "⟦ " e:lurk_expr " ⟧" : term =>
  elabLurkExpr e

namespace Lurk.SExpr.Tests

def names := ["a", "b", "c"]
def name := "d"

#eval IO.print ⟦
  (lambda ($names $name e) ())
⟧.print

#eval IO.print ⟦ (lambda (n) n) ⟧.print
-- (lambda (n)
--   n)

#eval IO.print ⟦
(let (
    (foo (lambda (a) (a)))
    (bar (lambda (x) (x))))
  (foo "1" 2 3))
⟧.print
-- (let (
--     (foo
--       (lambda (a)
--         (a)))
--     (bar
--       (lambda (x)
--         (x))))
--   (foo
--     "1"
--     2
--     3))

#eval IO.print ⟦
(let ((foo (lambda (a b c)
             (* (+ a b) c))))
  (foo "1" 2 3))
⟧.print
-- (let (
--     (foo
--       (lambda (a b c)
--         (*
--           (+
--             a
--             b)
--           c))))
--   (foo
--     "1"
--     2
--     3))

#eval IO.print ⟦
(let ()
  (foo "1" 2 3))
⟧.print
-- (let ()
--   (foo
--     "1"
--     2
--     3))

#eval IO.print ⟦
("s")
⟧.print
-- ("s")

def m := 1
def n := [[1, 2], []]

#eval IO.print ⟦
(quote ($n $m "s" n))
⟧.print
-- (quote (((1 2) ()) 1 "s"))

def test := [SExpr| 
  ($n $m "s")
]

#eval IO.print ⟦
  (quote ($test 1))
⟧.print
-- (quote ((((1 2) ()) 1 "s") 1))

def name2 := ["hi"]

#eval IO.print ⟦
  (lambda ($name2) ,($name . 3 . $name2))
⟧.print