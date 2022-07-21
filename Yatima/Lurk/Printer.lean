import Lurk.AST

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

partial def Expr.print : Expr → String
  | .lit l => toString l
  | .ifE test c alt => s!"(if {print test} {print c} {print alt})"
  | .lam formals body => 
    let formalsText := " ".intercalate (formals.map toString)
    s!"(lambda ({formalsText}) {print body})"
  | .letE bindings body => 
    let bindingsTextList := bindings.map fun (name, expr) => s!"({name} {expr.print})"
    let bindingsText := " ".intercalate bindingsTextList
    s!"(let ({bindingsText}) {print body})"
  | .letRecE bindings body => 
    let bindingsTextList := bindings.map fun (name, expr) => s!"({name} {expr.print})"
    let bindingsText := " ".intercalate bindingsTextList
    s!"(let ({bindingsText}) {print body})"
  | .app fn args => 
    let args := " ".intercalate (args.map print)
    let argPP := if args.length == 0 then "" else " "
    s!"({print fn}{argPP}{args})"
  | .quote datum => s!"(quote {datum.print})"
  | .unaryOp op expr => s!"({op} {print expr})"
  | .binOp op expr₁ expr₂ => s!"({op} {print expr₁} {print expr₂})"
  | .emit expr => s!"(emit {print expr})"
  | .begin exprs => 
    let exprs_text := " ".intercalate (exprs.map print)
    s!"(begin {exprs_text})"
  | .currEnv => "(current-env)"
  | .eval expr₁ expr₂? => match expr₂? with 
    | some expr₂ => s!"(eval {print expr₁} {print expr₂})"
    | none => s!"(eval {print expr₁})"

end Lurk
