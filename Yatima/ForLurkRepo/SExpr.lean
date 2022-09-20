import Lean
import Yatima.ForLurkRepo.Literal

open Std 

namespace Lurk 

inductive SExpr where
  | lit : Literal → SExpr
  | cons : SExpr → SExpr → SExpr
  deriving Repr, BEq, Inhabited

namespace SExpr

open Format ToFormat in 
partial def pprint (e : SExpr) (pretty := true) : Format :=
  match e with
  | .lit l     => format l
  | e@(.cons ..) => 
    let (es, tail) := telescopeCons [] e
      let tail := match tail with
      | .lit Literal.nil => Format.nil
      | _ => line ++ "." ++ line ++ pprint tail pretty
      paren <| fmtList es ++ tail
where 
  telescopeCons (acc : List SExpr) (e : SExpr) := match e with
    | .cons e₁ e₂ => telescopeCons (e₁ :: acc) e₂
    | _ => (acc.reverse, e)
  fmtList (xs : List SExpr) := match xs with
    | [ ]   => Format.nil
    | [n]   => format (pprint n pretty)
    | n::ns => format (pprint n pretty) ++ line ++ fmtList ns

def mkListWith (es : List SExpr) (tail : SExpr) : SExpr := 
  es.foldr (fun e acc => .cons e acc) tail

def mkList (es : List SExpr) := mkListWith es (.lit .nil)

instance : ToFormat SExpr where 
  format := pprint

class ToSExpr (α : Type u) where 
  toSExpr : α → SExpr

instance : ToSExpr Nat where 
  toSExpr n := .lit $ .num $ Fin.ofNat n

instance : ToSExpr String where 
  toSExpr s := .lit $ .str s

instance : ToSExpr Char where 
  toSExpr c := .lit $ .char c

instance [ToSExpr α] : ToSExpr (List α) where 
  toSExpr as := mkList (as.map ToSExpr.toSExpr)

instance [ToSExpr α] : ToSExpr (Array α) where 
  toSExpr as := mkList (as.toList.map ToSExpr.toSExpr)

instance : ToSExpr SExpr where 
  toSExpr s := s

end SExpr
end Lurk 

open Lean Elab Meta Term
declare_syntax_cat           sexpr
syntax lurk_literal        : sexpr
syntax "(" sexpr* ")"      : sexpr
syntax sexpr " . " sexpr   : sexpr

open Lurk SExpr in 
partial def elabSExpr : Syntax → TermElabM Lean.Expr
  | `(sexpr| $l:lurk_literal) => do
    mkAppM ``SExpr.lit #[← elabLiteral l]
  | `(sexpr| ($es*)) => do
    let es ← (es.mapM fun e => elabSExpr e)
    mkAppM ``mkList #[← mkListLit (mkConst ``SExpr) es.toList]
  | `(sexpr| $e1 . $e2) => do
    mkAppM ``SExpr.cons #[← elabSExpr e1, ← elabSExpr e2]
  | `(sexpr| $i) => do 
    if i.raw.isAntiquot then 
      let stx := i.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``ToSExpr.toSExpr #[e]
    else 
      throwUnsupportedSyntax 

elab "[SExpr| " e:sexpr "]" : term =>
  elabSExpr e
