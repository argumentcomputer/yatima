import Yatima.ForLurkRepo.AST
import YatimaStdLib.String

namespace Lurk.Expr

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

partial def printLit (l : Literal) (pretty := true) : String :=
  match l with 
  | .nil    => "nil"
  | .t      => "t"
  | .num n  => toString n
  | .sym n  => fixName n pretty
  | .str s  => s!"\"{s}\""
  | .char c => s!"#\\{c}"

instance : ToString Literal where 
  toString := printLit

open String (blankIndent) in
partial def print (e : Expr) (pretty := true) : String :=
  let rec aux (n : Nat) (p : Bool) : Expr → String
    | .lit l => s!"{blankIndent n}{printLit l pretty}"
    | .ifE test c alt => s!"{blankIndent n}(if\n{aux (n + 1) p test}\n{aux (n + 1) p c}\n{aux (n + 1) p alt})"
    | .lam formals body => s!"{blankIndent n}(lambda ({" ".intercalate (formals.map fun n => fixName n p)})\n{aux (n + 1) p body})"
    | .letE bindings body =>
      let bindingsStr := bindings.map
        fun (name, expr) => s!"{blankIndent (n + 2)}({fixName name p}\n{aux (n + 3) p expr})"
      s!"{blankIndent n}(let ({if bindingsStr.isEmpty then "" else "\n"}{"\n".intercalate bindingsStr})\n{aux (n + 1) p body})"
    | .letRecE bindings body =>
      let bindingsStr := bindings.map
        fun (name, expr) => s!"{blankIndent (n + 2)}({fixName name p}\n{aux (n + 3) p expr})"
      s!"{blankIndent n}(letrec ({if bindingsStr.isEmpty then "" else "\n"}{"\n".intercalate bindingsStr})\n{aux (n + 1) p body})"
    | .app fn args =>
      let args := "\n".intercalate $ args.map (aux (n + 1) p)
      s!"{blankIndent n}({fn.print p}{if args.isEmpty then "" else "\n"}{args})"
    | .quote datum => s!"{blankIndent n}(quote {datum.print })"
    | .unaryOp op expr => s!"{blankIndent n}({op}\n{aux (n + 1) p expr})"
    | .binOp op expr₁ expr₂ => s!"{blankIndent n}({op}\n{aux (n + 1) p expr₁}\n{aux (n + 1) p expr₂})"
    | .emit expr => s!"{blankIndent n}(emit\n{aux (n + 1) p expr})"
    | .begin exprs =>
      let exprs := "\n".intercalate (exprs.map $ aux (n + 1) p)
      s!"{blankIndent n}(begin{if exprs.isEmpty then "" else "\n"}{exprs})"
    | .currEnv => s!"{blankIndent n}(current-env)"
    | .eval expr₁ expr₂? => match expr₂? with
      | some expr₂ => s!"{blankIndent n}(eval\n{aux (n + 1) p expr₁}\n{aux (n + 1) p expr₂})"
      | none => s!"{blankIndent n}(eval\n{aux (n + 1) p expr₁})"
  aux 0 pretty e

instance : ToString Expr where 
  toString := print

end Lurk.Expr
