import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk
open Std 

abbrev Frame := Std.RBMap Name Expr compare

abbrev Env := List Frame

inductive Value where 
  | lit : Literal → Value 
  | lam : List Name → Expr → Value 
  | raw : SExpr → Value
  deriving Repr, BEq

instance : Inhabited Value where 
  default := .lit .nil

open Std.Format Std.ToFormat in
partial def Value.pprint (v : Value) (pretty := true) : Std.Format :=
  match v with 
    | .lit l => format l 
    | .lam ns e => 
      paren <| group ("lambda" ++ line ++ paren (fmtNames ns)) ++ line ++ e.pprint pretty
    | .raw s => s.pprint pretty
  where 
    fmtNames (xs : List Name) := match xs with 
      | [] => Format.nil
      | [n]  => format $ fixName n pretty
      | n::ns => format (fixName n pretty) ++ line ++ fmtNames ns

instance : ToFormat Value where 
  format := Value.pprint

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
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x * y)  
    | _, _ => throw "error: not a number"
  | .quot => match v₁, v₂ with 
    | .lit (.num x), .lit (.num y) => return .lit $ .num (x * y⁻¹)  
    | _, _ => throw "error: not a number" 
  | .eq => match v₁, v₂ with 
    | .lit (.num x), .lit (.num y) => 
      return if x == y then .lit .t else .lit .nil
    | _, _ => throw "error: not a number"
  | .nEq => return if v₁ == v₂ then .lit .t else .lit .nil 

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

def ppEval (e : Expr) (env : Env := default) : Format := 
  match evaluate e env with 
  | .ok res => res.pprint 
  | .error e => e

#eval ⟦,1⟧

end Lurk 