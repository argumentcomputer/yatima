import Yatima.ForLurkRepo.DSL
import Yatima.Compiler.Utils

namespace Lurk
open Std 

inductive Value where
  | lit : Literal → Value
  | lam : List Name → Expr → Value
  | raw : SExpr → Value
  | env : Std.RBMap Name Expr compare → Value
  deriving Repr, Inhabited

abbrev Env := Std.RBMap Name Value compare

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

def evalUnaryOp (op : UnaryOp) (v : Value) : EvalM Value := match op with
  | .car => default  
  | .cdr => default
  | .atom => default
  | .emit => default

def evalBinaryOp (op : BinaryOp) (v₁ v₂ : Value) : EvalM Value :=
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
  | .nEq => return if v₁ != v₂ then .lit .t else .lit .nil

def toBool : Value → EvalM Bool
  | .lit .t => return true
  | .lit .nil => return false
  | _ => throw "not a boolean"

mutual

partial def bind (env₀ : Env) (ns : List Name) (as : List Expr) :
    EvalM (Env × List Name) :=
  let rec aux : Env → List Name → List Expr → EvalM (Env × List Name)
    | env, n::ns, a::as => do bind (env.insert n (← evaluate env₀ a)) ns as
    | _, [], _::_ => throw ""
    | env, ns, [] => return (env, ns)
  aux env₀ ns as

partial def evaluate (env : Env) : Expr → EvalM Value
  | .lit lit => return .lit lit --FIX
  | .ifE tst con alt => do
    if ← toBool (← evaluate env tst)
      then evaluate env con
      else evaluate env alt
  | .lam formals body => return .lam formals body
  | .letE bindings body => default
  | .letRecE bindings body => default
  | .app fn args => do
    match ← evaluate env fn with
    | .lam ns body =>
      match ← bind env ns args with
      | (env', []) => evaluate env' body
      | (env', ns) => return .lam ns sorry
    | _ => throw "not a lambda"
  | .quote datum => default 
  | .unaryOp op e => do evalUnaryOp op (← evaluate env e)
  | .binaryOp op e₁ e₂ => do
    evalBinaryOp op (← evaluate env e₁) (← evaluate env e₂)
  | .emit e => default
  | .begin es => default
  | .currEnv => default
  | .eval e env? => default

end

end Interpreter

def evaluate (e : Expr) (env : Env := default) : Except String Value := 
  match Interpreter.EvalM.run () ⟨env⟩ (Interpreter.evaluate env e) with 
  | .ok res _ => .ok res 
  | .error e _ => .error e

def ppEval (e : Expr) (env : Env := default) : Format := 
  match evaluate e env with 
  | .ok res => res.pprint 
  | .error e => e

#eval ⟦,1⟧

end Lurk 