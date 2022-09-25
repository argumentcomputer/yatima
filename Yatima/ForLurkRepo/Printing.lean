import Yatima.ForLurkRepo.AST
import YatimaStdLib.String

namespace Lurk.Expr
open Std

instance : ToFormat BinaryOp where format
  | .sum   => "+"
  | .diff  => "-"
  | .prod  => "*"
  | .quot  => "/"
  | .numEq => "="
  | .lt    => "<"
  | .gt    => ">"
  | .le    => "<="
  | .ge    => ">="
  | .eq    => "eq"

open Std.Format Std.ToFormat in
partial def pprint (e : Expr) (pretty := true) : Std.Format :=
  match e with
  | .lit l => format l
  | .sym n => bracket "|" (validate n) "|"
  | .ifE test con alt =>
    paren <| group ("if" ++ line ++ pprint test pretty) ++ line ++ pprint con pretty ++ line ++ pprint alt pretty
  | .lam formals body =>
    paren <| "lambda" ++ line ++ paren (fmtNames formals) ++ indentD (pprint body pretty)
  | .letE bindings body =>
    paren <| "let" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
  | .letRecE bindings body =>
    paren <| "letrec" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
  | .mutRecE bindings body =>
    paren <| "mutrec" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
  | .app₀ fn => paren <| pprint fn pretty
  | e@(.app ..) => 
    let (fn, args) := telescopeApp e []
    let args := if args.length == 0 then .nil else indentD (fmtList args)
    paren <| pprint fn pretty ++ args
  | .quote datum =>
    paren <| "quote" ++ line ++ datum.pprint pretty
  | .binaryOp op expr₁ expr₂ =>
    paren <| format op ++ line ++ pprint expr₁ pretty ++ line ++ pprint expr₂ pretty
  | .atom expr => paren <| "atom" ++ line ++ pprint expr pretty
  | .cdr expr => paren <| "cdr" ++ line ++ pprint expr pretty
  | .car expr => paren <| "car" ++ line ++ pprint expr pretty
  | .emit expr => paren <| "emit" ++ line ++ pprint expr pretty
  | .cons e₁ e₂ =>
    paren <| group ("cons" ++ line ++ pprint e₁ pretty) ++ line ++ pprint e₂ pretty
  | .strcons e₁ e₂ =>
    paren <| group ("strcons" ++ line ++ pprint e₁ pretty) ++ line ++ pprint e₂ pretty
  | .begin exprs => paren <| "begin" ++ line ++ fmtList exprs
  | .currEnv => "current-env"
where
  fmtNames (xs : List Name) := match xs with
    | [] => Format.nil
    | [n]  => bracket "|" (validate n) "|"
    | n::ns => bracket "|" (validate n) "|" ++ line ++ fmtNames ns
  fmtList (xs : List Expr) := match xs with
    | [] => Format.nil
    | [e]  => pprint e pretty
    | e::es => pprint e pretty ++ line ++ fmtList es
  fmtBinds (xs : List (Name × Expr)) := match xs with
    | [] => Format.nil
    | [(n, e)]  => paren <| bracket "|" (validate n) "|" ++ line ++ pprint e pretty
    | (n, e)::xs =>
      (paren $ bracket "|" (validate n) "|" ++ line ++ pprint e pretty)
        ++ line ++ fmtBinds xs
  telescopeApp (e : Expr) (args : List Expr) := match e with 
    | .app fn arg => telescopeApp fn <| arg :: args
    | _ => (e, args)

instance : ToFormat Expr where
  format := pprint

end Lurk.Expr
