import Lean
import Yatima.ForLurkRepo.FixName

namespace Lurk 

inductive SExpr where
  | atom : Name → SExpr
  | num  : Int → SExpr
  | str  : String → SExpr
  | char : Char → SExpr
  | list : List SExpr → SExpr
  | cons : SExpr → SExpr → SExpr
  deriving Repr

namespace SExpr

partial def print : SExpr → String
  | .atom s     => fixName s
  | .num  n     => s!"{n}"
  | .str  s     => s!"\"{s}\""
  | .char c     => s!"\'{c}\'"
  | .list es    => "(" ++ " ".intercalate (es.map SExpr.print) ++ ")"
  | .cons e1 e2 => s!"{e1.print} . {e2.print}"

instance : ToString SExpr where 
  toString := print

class ToSExpr (α : Type u) where 
  toSExpr : α → SExpr

instance : ToSExpr Nat where 
  toSExpr n := .num n
  
instance : ToSExpr Int where 
  toSExpr := .num

instance : ToSExpr Name where 
  toSExpr := .atom

instance : ToSExpr String where 
  toSExpr := .str

instance : ToSExpr Char where 
  toSExpr := .char

instance [ToSExpr α] : ToSExpr (List α) where 
  toSExpr as := .list (as.map ToSExpr.toSExpr)

instance [ToSExpr α] : ToSExpr (Array α) where 
  toSExpr as := .list (as.toList.map ToSExpr.toSExpr)

instance : ToSExpr SExpr where 
  toSExpr s := s

end SExpr
end Lurk 

open Lean Elab Meta Term
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

open Lurk.SExpr in 
partial def elabSExpr : Syntax → TermElabM Expr
  | `(sexpr| -$n:num) => match n.getNat with
    | 0     => do
      mkAppM ``Lurk.SExpr.num #[← mkAppM ``Int.ofNat #[mkConst ``Nat.zero]]
    | n + 1 => do
      mkAppM ``Lurk.SExpr.num #[← mkAppM ``Int.negSucc #[mkNatLit n]]
  | `(sexpr| $n:num) => do
    mkAppM ``Lurk.SExpr.num #[← mkAppM ``Int.ofNat #[mkNatLit n.getNat]]
  | `(sexpr| $i:ident) => do 
    mkAppM ``Lurk.SExpr.atom #[← mkNameLit i.getId.toString]
  | `(sexpr| +) => do mkAppM ``Lurk.SExpr.atom #[← mkNameLit "+"]
  | `(sexpr| -) => do mkAppM ``Lurk.SExpr.atom #[← mkNameLit "-"]
  | `(sexpr| *) => do mkAppM ``Lurk.SExpr.atom #[← mkNameLit "*"]
  | `(sexpr| /) => do mkAppM ``Lurk.SExpr.atom #[← mkNameLit "/"]
  | `(sexpr| =) => do mkAppM ``Lurk.SExpr.atom #[← mkNameLit "/"]
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
      let e ← whnf e
      mkAppM ``ToSExpr.toSExpr #[e]
    else 
      throwUnsupportedSyntax 
  | _ => throwUnsupportedSyntax
  where 
    mkNameLit (name : String) := 
      mkAppM ``Name.mkSimple #[mkStrLit name]

elab "[SExpr| " e:sexpr "]" : term =>
  elabSExpr e
