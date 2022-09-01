import Lean
import Yatima.ForLurkRepo.Printing
import Yatima.ForLurkRepo.Utils

open Lean Elab Meta Term

def mkNameLit (name : String) := 
  mkAppM ``Name.mkSimple #[mkStrLit name]

declare_syntax_cat    lurk_literal
syntax "t"          : lurk_literal
syntax "nil"        : lurk_literal
-- syntax "-" noWs num : lurk_literal
syntax num          : lurk_literal
syntax str          : lurk_literal
syntax char         : lurk_literal

def elabLurkLiteral : Syntax → TermElabM Expr
  | `(lurk_literal| t)   => return mkConst ``Lurk.Literal.t
  | `(lurk_literal| nil) => return mkConst ``Lurk.Literal.nil
  -- | `(lurk_literal| -$n) => match n.getNat with
  --   | 0     => do
  --     mkAppM ``Lurk.Literal.num #[← mkAppM ``Fin.ofNat #[mkConst ``Nat.zero]]
  --   | n + 1 => do
  --     mkAppM ``Lurk.Literal.num #[← mkAppM ``Fin.ofInt #[← mkAppM ``Int.negSucc #[mkNatLit n]]]
  | `(lurk_literal| $n:num) => do
    mkAppM ``Lurk.mkNumLit #[mkNatLit n.getNat]
  | `(lurk_literal| $s:str) =>
    mkAppM ``Lurk.Literal.str #[mkStrLit s.getString]
  | `(lurk_literal| $c:char) => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``Lurk.Literal.char #[c]
  | _ => throwUnsupportedSyntax

declare_syntax_cat  lurk_bin_op
syntax "+ "       : lurk_bin_op
syntax "- "       : lurk_bin_op
syntax "* "       : lurk_bin_op
syntax "/ "       : lurk_bin_op
syntax "= "       : lurk_bin_op
syntax "eq "      : lurk_bin_op

def elabLurkBinOp : Syntax → TermElabM Expr
  | `(lurk_bin_op| +)    => return mkConst ``Lurk.BinaryOp.sum
  | `(lurk_bin_op| -)    => return mkConst ``Lurk.BinaryOp.diff
  | `(lurk_bin_op| *)    => return mkConst ``Lurk.BinaryOp.prod
  | `(lurk_bin_op| /)    => return mkConst ``Lurk.BinaryOp.quot
  | `(lurk_bin_op| =)    => return mkConst ``Lurk.BinaryOp.eq
  | `(lurk_bin_op| eq)   => return mkConst ``Lurk.BinaryOp.nEq -- unfortunate clash again
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_expr
declare_syntax_cat lurk_binding
declare_syntax_cat lurk_bindings

syntax "(" ident lurk_expr ")" : lurk_binding
syntax  "(" lurk_binding* ")"  : lurk_bindings

syntax lurk_literal                               : lurk_expr
syntax ident                                      : lurk_expr
syntax "(" "if" lurk_expr lurk_expr lurk_expr ")" : lurk_expr
syntax "(" "lambda" "(" ident* ")" lurk_expr ")"  : lurk_expr
syntax "(" "let" lurk_bindings lurk_expr ")"      : lurk_expr
syntax "(" "letrec" lurk_bindings lurk_expr ")"   : lurk_expr
syntax "(" "quote " sexpr ")"                     : lurk_expr
syntax "," sexpr                                  : lurk_expr
syntax "(" lurk_bin_op lurk_expr lurk_expr ")"    : lurk_expr
syntax "(" "car" lurk_expr ")"                    : lurk_expr
syntax "(" "cdr" lurk_expr ")"                    : lurk_expr
syntax "(" "atom" lurk_expr ")"                   : lurk_expr
syntax "(" "emit" lurk_expr ")"                   : lurk_expr
syntax "(" "cons" lurk_expr lurk_expr ")"         : lurk_expr
syntax "(" "strcons" lurk_expr lurk_expr ")"      : lurk_expr
syntax "(" "begin" lurk_expr*  ")"                : lurk_expr
syntax "current-env"                              : lurk_expr
syntax "(" lurk_expr* ")"                         : lurk_expr

/-- 
There are no type guarentees. 
-/
partial def elabLurkIdents (i : TSyntax `ident) : TermElabM Expr := do 
  if i.raw.isAntiquot then 
    let stx := i.raw.getAntiquotTerm
    let e ← elabTerm stx none
    let e ← whnf e
    let type ← inferType e
    match type.getAppFn with 
    | .const ``List _ => return e
    | _ => 
      let «nil» ← mkAppOptM ``List.nil #[some (mkConst ``Lurk.Name)]
      mkAppM ``List.cons #[e, «nil»]
  else
    let «nil» ← mkAppOptM ``List.nil #[some (mkConst ``Lurk.Name)]
    mkAppM ``List.cons #[← mkNameLit i.getId.toString, «nil»]


mutual 
partial def elabLurkBinding : Syntax → TermElabM Expr 
  | `(lurk_binding| ($name $body)) => do
    mkAppM ``Prod.mk #[← mkNameLit name.getId.toString, ← elabLurkExpr body]
  | _ => throwUnsupportedSyntax

partial def elabLurkBindings : Syntax → TermElabM Expr 
  | `(lurk_bindings| ($bindings*)) => do 
    let bindings ← bindings.mapM elabLurkBinding
    let type ← mkAppM ``Prod #[mkConst ``Lurk.Name, mkConst ``Lurk.Expr]
    mkListLit type bindings.toList
  | _ => throwUnsupportedSyntax

partial def elabLurkExpr : TSyntax `lurk_expr → TermElabM Expr
  | `(lurk_expr| $l:lurk_literal) => do
    mkAppM ``Lurk.Expr.lit #[← elabLurkLiteral l]
  | `(lurk_expr| $i:ident) => do
    mkAppM ``Lurk.Expr.sym #[← mkNameLit i.getId.toString]
  | `(lurk_expr| (if $test $con $alt)) => do
    mkAppM ``Lurk.Expr.ifE
      #[← elabLurkExpr test, ← elabLurkExpr con, ← elabLurkExpr alt]
  | `(lurk_expr| (lambda ($formals*) $body)) => do
    let formals ← Array.toList <$> formals.mapM elabLurkIdents
    let formals ← mkListLit (← mkAppM ``List #[mkConst ``Lurk.Name]) formals
    let formals ← mkAppM ``List.join #[formals]
    mkAppM ``Lurk.Expr.lam #[formals, ← elabLurkExpr body]
  | `(lurk_expr| (let $bind $body)) => do
    mkAppM ``Lurk.Expr.letE #[← elabLurkBindings bind, ← elabLurkExpr body]
  | `(lurk_expr| (letrec $bind $body)) => do
    mkAppM ``Lurk.Expr.letRecE #[← elabLurkBindings bind, ← elabLurkExpr body]
  | `(lurk_expr| (quote $datum)) => do
    mkAppM ``Lurk.Expr.quote #[← elabSExpr datum]
  | `(lurk_expr| ,$datum) => do
    mkAppM ``Lurk.Expr.quote #[← elabSExpr datum]
  | `(lurk_expr| ($op:lurk_bin_op $e1 $e2)) => do
    mkAppM ``Lurk.Expr.binaryOp
      #[← elabLurkBinOp op, ← elabLurkExpr e1, ← elabLurkExpr e2]
  | `(lurk_expr| (car $e)) => do mkAppM ``Lurk.Expr.car #[← elabLurkExpr e]
  | `(lurk_expr| (cdr $e)) => do mkAppM ``Lurk.Expr.cdr #[← elabLurkExpr e]
  | `(lurk_expr| (atom $e)) => do mkAppM ``Lurk.Expr.atom #[← elabLurkExpr e]
  | `(lurk_expr| (emit $e)) => do mkAppM ``Lurk.Expr.emit #[← elabLurkExpr e]
  | `(lurk_expr| (cons $e₁ $e₂)) => do
    mkAppM ``Lurk.Expr.cons #[← elabLurkExpr e₁, ← elabLurkExpr e₂]
  | `(lurk_expr| (strcons $e₁ $e₂)) => do
    mkAppM ``Lurk.Expr.strcons #[← elabLurkExpr e₁, ← elabLurkExpr e₂]
  | `(lurk_expr| (begin $es*)) => do
    let es := (← es.mapM elabLurkExpr).toList
    let type := Lean.mkConst ``Lurk.Expr
    mkAppM ``Lurk.Expr.begin #[← mkListLit type es]
  | `(lurk_expr| current-env) => return mkConst ``Lurk.Expr.currEnv
  | `(lurk_expr| ($e*)) => do
    let e := (← e.mapM elabLurkExpr).toList
    match e with 
    | []   => 
      let s ← mkAppM ``Lurk.Expr.sym #[← mkNameLit "()"]
      mkAppM ``Lurk.Expr.lit #[s]
    | e::es => 
      let type := Lean.mkConst ``Lurk.Expr
      mkAppM ``Lurk.Expr.app #[e, ← mkListLit type es]
  | `(lurk_expr| $i) => do 
    if i.raw.isAntiquot then 
      let stx := i.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``Lurk.Expr.ToExpr.toExpr #[e]
    else 
      throwUnsupportedSyntax 
end

--#eval Name.mkSimple ""

elab "⟦ " e:lurk_expr " ⟧" : term =>
  elabLurkExpr e

namespace Lurk.Expr 

def mkMutualBlock (mutuals : List (Name × Expr)) : List (Name × Expr) :=
  let names := mutuals.map Prod.fst
  let mutualName := names.head! ++ `mutual
  let fnProjs := names.enum.map fun (i, (n : Name)) => (n, app ⟦$mutualName⟧ [⟦$i⟧])
  let targets := fnProjs.map fun (n, e) => (⟦$n⟧, e)
  let mutualBlock := mkIfElses (mutuals.enum.map fun (i, _, e) =>
    (⟦(= mutidx $i)⟧, e.replaceN targets)  
  ) ⟦nil⟧
  (mutualName, ⟦(lambda (mutidx) $mutualBlock)⟧) :: fnProjs



end Lurk.Expr 