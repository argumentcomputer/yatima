import Yatima.ForLurkRepo.DSL

namespace Lurk 

def Expr.mkNum (n : Nat) : Expr := 
  .lit $ .num n

def Expr.isNum (e : Expr) : Bool := 
  match e with | .lit $ .num _ => true | _ => false
  
def Expr.eqNum (e : Expr) (n : Nat) : Bool := 
  match e with | .lit $ .num m => n == m | _ => false

def Expr.mkStr (s : String) : Expr := 
  .lit $ .str s

def Expr.isStr (e : Expr) : Bool := 
  match e with | .lit $ .str _ => true | _ => false

def Expr.eqStr (e : Expr) (s₁ : String) : Bool := 
  match e with | .lit $ .str s₂ => s₁ == s₂ | _ => false

def Expr.mkIfElses (ifThen : List (Expr × Expr)) (finalElse : Expr) : Expr := 
  match ifThen with 
  | [] => .lit .nil 
  | [(cond, body)] => .ifE cond body finalElse
  | (cond, body) :: es => .ifE cond body (Expr.mkIfElses es finalElse)

end Lurk 