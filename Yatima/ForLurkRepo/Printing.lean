import Yatima.ForLurkRepo.AST
import YatimaStdLib.String

namespace Lurk.Expr
open Std 

instance : ToFormat UnaryOp where format
  | .car  => "car"
  | .cdr  => "cdr"
  | .atom => "atom"
  | .emit => "emit"

instance : ToFormat BinOp where format
  | .cons    => "cons"
  | .strcons => "strcons"
  | .sum     => "+"
  | .diff    => "-"
  | .prod    => "*"
  | .quot    => "/"  
  | .eq      => "="
  | .nEq     => "eq" -- NOTE: This was an unfortunate choice, maybe swap definitions in the AST?

partial def pprintLit (l : Literal) (pretty := true) : Format :=
  match l with 
  | .nil    => "nil"
  | .t      => "t"
  | .num n  => toString n
  | .sym n  => fixName n pretty
  | .str s  => s!"\"{s}\""
  | .char c => s!"#\\{c}"

instance : ToFormat Literal where 
  format := pprintLit

open Std.Format Std.ToFormat in
partial def pprint (e : Expr) (pretty := true) : Std.Format :=
  match e with 
    | .lit l => format l
    | .ifE test con alt => 
      paren <| group ("if" ++ line ++ pprint test pretty) ++ line ++ pprint con pretty ++ line ++ pprint alt pretty
    | .lam formals body => 
      paren <| group ("lambda" ++ line ++ paren (fmtNames formals)) ++ line ++ pprint body pretty
    | .letE bindings body => 
      paren <| "let" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
    | .letRecE bindings body =>
      paren <| "letrec" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty
    | .app fn args => 
      paren <| pprint fn ++ if args.length != 0 then line ++ fmtList args else nil
    | .quote datum => 
      paren <| "quote" ++ line ++ datum.pprint pretty
    | .unaryOp op expr => 
      paren <| format op ++ line ++ pprint expr pretty
    | .binOp op expr₁ expr₂ => 
      paren <| format op ++ line ++ pprint expr₁ pretty ++ line ++ pprint expr₂ pretty
    | .emit expr => 
      paren <| "emit" ++ line ++ pprint expr pretty
    | .begin exprs =>
      paren <| "begin" ++ line ++ fmtList exprs
    | .currEnv => "current-env"
    | .eval expr₁ expr₂? => match expr₂? with
      | some expr₂ => paren <| "eval" ++ line ++ pprint expr₁ pretty ++ line ++ pprint expr₂ pretty
      | none => paren <| "eval" ++ line ++ pprint expr₁ pretty ++ line
  where 
    fmtNames (xs : List Name) := match xs with 
      | [] => nil
      | [n]  => format n
      | n::ns => format n ++ line ++ fmtNames ns
    fmtList (xs : List Expr) := match xs with 
      | [] => nil
      | [e]  => pprint e pretty
      | e::es => pprint e pretty ++ line ++ fmtList es
    fmtBinds (xs : List (Name × Expr)) := match xs with 
      | [] => nil
      | [(n, e)]  => paren <| format n ++ line ++ pprint e pretty
      | (n, e)::xs => (paren $ format n ++ line ++ pprint e pretty) ++ line ++ fmtBinds xs
  
instance : ToFormat Expr where 
  format := pprint

-- open String (blankIndent) in
-- partial def print (e : Expr) (pretty := true) : String :=
--   let rec aux (n : Nat) (p : Bool) : Expr → String
--     | .lit l => s!"{blankIndent n}{printLit l pretty}"
--     | .ifE test c alt => s!"{blankIndent n}(if\n{aux (n + 1) p test}\n{aux (n + 1) p c}\n{aux (n + 1) p alt})"
--     | .lam formals body => s!"{blankIndent n}(lambda ({" ".intercalate (formals.map fun n => fixName n p)})\n{aux (n + 1) p body})"
--     | .letE bindings body =>
--       let bindingsStr := bindings.map
--         fun (name, expr) => s!"{blankIndent (n + 2)}({fixName name p}\n{aux (n + 3) p expr})"
--       s!"{blankIndent n}(let ({if bindingsStr.isEmpty then "" else "\n"}{"\n".intercalate bindingsStr})\n{aux (n + 1) p body})"
--     | .letRecE bindings body =>
--       let bindingsStr := bindings.map
--         fun (name, expr) => s!"{blankIndent (n + 2)}({fixName name p}\n{aux (n + 3) p expr})"
--       s!"{blankIndent n}(letrec ({if bindingsStr.isEmpty then "" else "\n"}{"\n".intercalate bindingsStr})\n{aux (n + 1) p body})"
--     | .app fn args =>
--       let args := "\n".intercalate $ args.map (aux (n + 1) p)
--       s!"{blankIndent n}({fn.print p}{if args.isEmpty then "" else "\n"}{args})"
--     | .quote datum => s!"{blankIndent n}(quote {datum.print })"
--     | .unaryOp op expr => s!"{blankIndent n}({op}\n{aux (n + 1) p expr})"
--     | .binOp op expr₁ expr₂ => s!"{blankIndent n}({op}\n{aux (n + 1) p expr₁}\n{aux (n + 1) p expr₂})"
--     | .emit expr => s!"{blankIndent n}(emit\n{aux (n + 1) p expr})"
--     | .begin exprs =>
--       let exprs := "\n".intercalate (exprs.map $ aux (n + 1) p)
--       s!"{blankIndent n}(begin{if exprs.isEmpty then "" else "\n"}{exprs})"
--     | .currEnv => s!"{blankIndent n}(current-env)"
--     | .eval expr₁ expr₂? => match expr₂? with
--       | some expr₂ => s!"{blankIndent n}(eval\n{aux (n + 1) p expr₁}\n{aux (n + 1) p expr₂})"
--       | none => s!"{blankIndent n}(eval\n{aux (n + 1) p expr₁})"
--   aux 0 pretty e

end Lurk.Expr
