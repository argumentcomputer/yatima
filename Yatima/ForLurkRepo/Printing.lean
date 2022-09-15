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

partial def pprintLit (l : Literal) (pretty := true) : Format :=
  match l with
  | .nil        => "nil"
  | .t          => "t"
  | .num ⟨n, _⟩ => if n < USize.size then toString n else List.asString (Nat.toDigits 16 n)
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

instance : ToFormat Literal where
  format := pprintLit

open Std.Format Std.ToFormat in
partial def pprint (e : Expr) (pretty := true) : Std.Format :=
  match e with
  | .lit l => pprintLit l pretty
  | .sym n => fixName n pretty
  | .ifE test con alt =>
    paren <| group ("if" ++ line ++ pprint test pretty) ++ line ++ pprint con pretty ++ line ++ pprint alt pretty
  | .lam formals body =>
    paren <| group ("lambda" ++ line ++ paren (fmtNames formals)) ++ line ++ pprint body pretty
  | .letE bindings body =>
    paren <| "let" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
  | .letRecE bindings body =>
    paren <| "letrec" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
  | .mutRecE bindings body =>
    paren <| "mutrec" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
  | .app₀ fn => paren <| pprint fn pretty
  | e@(.app ..) => 
    let (fn, args) := telescopeApp e []
    let ws := if args.length == 0 then Format.nil else " "
    paren <| pprint fn pretty ++ ws ++ group (fmtList args)
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
    | [] => nil
    | [n]  => format $ fixName n pretty
    | n::ns => format (fixName n pretty) ++ line ++ fmtNames ns
  fmtList (xs : List Expr) := match xs with
    | [] => nil
    | [e]  => pprint e pretty
    | e::es => pprint e pretty ++ line ++ fmtList es
  fmtBinds (xs : List (Name × Expr)) := match xs with
    | [] => nil
    | [(n, e)]  => paren <| format (fixName n pretty) ++ line ++ pprint e pretty
    | (n, e)::xs =>
      (paren $ format (fixName n pretty) ++ line ++ pprint e pretty)
        ++ line ++ fmtBinds xs
  telescopeApp (e : Expr) (args : List Expr) := match e with 
    | .app fn arg => telescopeApp fn <| arg :: args
    | _ => (e, args)

instance : ToFormat Expr where
  format := pprint

end Lurk.Expr
