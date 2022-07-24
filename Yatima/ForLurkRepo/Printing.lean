import Yatima.ForLurkRepo.AST
import YatimaStdLib.String

namespace Lurk

instance : ToString UnaryOp where toString
  | .car  => "car"
  | .cdr  => "cdr"
  | .atom => "atom"
  | .emit => "emit"

instance : ToString BinOp where toString
  | .cons    => "cons"
  | .strcons => "strcons"
  | .sum     => "+"
  | .diff    => "-"
  | .prod    => "*"
  | .quot    => "/"  
  | .eq      => "="
  | .nEq     => "eq" -- NOTE: This was an unfortunate choice, maybe swap definitions in the AST?

instance : ToString Literal where toString
  | .nil    => "nil"
  | .t      => "t"
  | .num n  => toString n
  | .sym n  => toString n
  | .str s  => s!"\"{s}\""
  | .char c => s!"#\\{c}"

partial def SExpr.print : SExpr → String
  | .atom s     => s
  | .num  n     => s!"{n}"
  | .str  s     => s!"\"{s}\""
  | .char c     => s!"\'{c}\'"
  | .list es    => "(" ++ " ".intercalate (es.map SExpr.print) ++ ")"
  | .cons e1 e2 => s!"{e1.print} . {e2.print}"

open String (blankIndent) in
partial def Expr.print (e : Expr) : String :=
  let rec aux (n : Nat) : Expr → String
    | .lit l => s!"{blankIndent n}{toString l}"
    | .ifE test c alt => s!"{blankIndent n}(if\n{aux (n + 1) test}\n{aux (n + 1) c}\n{aux (n + 1) alt})"
    | .lam formals body => s!"{blankIndent n}(lambda ({" ".intercalate formals})\n{aux (n + 1) body})"
    | .letE bindings body =>
      let bindingsStr := bindings.map
        fun (name, expr) => s!"{blankIndent (n + 2)}({name}\n{aux (n + 3) expr})"
      s!"{blankIndent n}(let ({if bindingsStr.isEmpty then "" else "\n"}{"\n".intercalate bindingsStr})\n{aux (n + 1) body})"
    | .letRecE bindings body =>
      let bindingsStr := bindings.map
        fun (name, expr) => s!"{blankIndent (n + 2)}({name}\n{aux (n + 3) expr})"
      s!"{blankIndent n}(letrec ({if bindingsStr.isEmpty then "" else "\n"}{"\n".intercalate bindingsStr})\n{aux (n + 1) body})"
    | .app fn args =>
      let args := "\n".intercalate $ args.map (aux (n + 1))
      s!"{blankIndent n}({fn.print}{if args.isEmpty then "" else "\n"}{args})"
    | .quote datum => s!"{blankIndent n}(quote {datum.print})"
    | .unaryOp op expr => s!"{blankIndent n}({op}\n{aux (n + 1) expr})"
    | .binOp op expr₁ expr₂ => s!"{blankIndent n}({op}\n{aux (n + 1) expr₁}\n{aux (n + 1) expr₂})"
    | .emit expr => s!"{blankIndent n}(emit\n{aux (n + 1) expr})"
    | .begin exprs =>
      let exprs := "\n".intercalate (exprs.map $ aux (n + 1))
      s!"{blankIndent n}(begin{if exprs.isEmpty then "" else "\n"}{exprs})"
    | .currEnv => s!"{blankIndent n}(current-env)"
    | .eval expr₁ expr₂? => match expr₂? with
      | some expr₂ => s!"{blankIndent n}(eval\n{aux (n + 1) expr₁}\n{aux (n + 1) expr₂})"
      | none => s!"{blankIndent n}(eval\n{aux (n + 1) expr₁})"
  aux 0 e

end Lurk
