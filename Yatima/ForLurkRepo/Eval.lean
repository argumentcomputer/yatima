import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk

-- Maybe something more complex?
abbrev Frame := Std.RBMap Name Expr compare

abbrev Env := List Frame

inductive Value where 
  | lit : Literal → Value 
  | lam : List Name → Expr → Value 
  | raw : SExpr → Value
  deriving Repr, BEq

instance : Inhabited Value where 
  default := .lit .nil

namespace Interpreter

structure State where 
  (env : Env)
  deriving Inhabited

abbrev Context := Unit 

abbrev EvalM := ReaderT Context $ EStateM String State

def EvalM.run (ctx : Context) (stt : State) (m : EvalM α) : 
    EStateM.Result String State α := 
  EStateM.run (ReaderT.run m ctx) stt 

mutual 

partial def evalUnaryOp (op : UnaryOp) (e : Expr) : EvalM Value := match op with
  | .car => default  
  | .cdr => default
  | .atom => default
  | .emit => default

partial def evalBinOp (op : BinOp) (e₁ e₂ : Expr) (env : Env) : EvalM Value := do 
  let v₁ ← evaluate e₁ env
  let v₂ ← evaluate e₂ env
  match op with 
  | .cons => default
  | .strcons => default
  | .sum => match v₁, v₂ with 
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x + y)  
    | _, _ => throw "error: not a number"
  | .diff => match v₁, v₂ with 
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x - y)  
    | _, _ => throw "error: not a number"
  | .prod => match v₁, v₂ with 
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x + y)  
    | _, _ => throw "error: not a number"
  | .quot => match v₁, v₂ with 
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x + y)  
    | _, _ => throw "error: not a number" 
  | .eq => default
  | .nEq => default 

partial def evaluate (e : Expr) (env : Env) : EvalM Value := do match e with 
  | .lit lit => return .lit lit 
  | .ifE tst con alt => default 
  | .lam formals body => default 
  | .letE bindings body => default 
  | .letRecE bindings body => default  
  | .app fn args => default 
  | .quote datum => default 
  | .unaryOp op e => default 
  | .binOp op e₁ e₂ => evalBinOp op e₁ e₂ env
  | .emit e => default 
  | .begin es => default 
  | .currEnv => default 
  | .eval e env? => default

end 

end Interpreter

def evaluate (e : Expr) (env : Env := default) : Except String Value := 
  match Interpreter.EvalM.run () ⟨env⟩ (Interpreter.evaluate e env) with 
  | .ok res _ => .ok res 
  | .error e _ => .error e

end Lurk 