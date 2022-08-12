import Lean 
import Yatima.ForLurkRepo.AST

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

def Expr.mkIfElses (ifThens : List (Expr × Expr)) (finalElse : Expr) : Expr := 
  match ifThens with 
  | [] => .lit .nil 
  | [(cond, body)] => .ifE cond body finalElse
  | (cond, body) :: es => .ifE cond body (Expr.mkIfElses es finalElse)

end Lurk 

namespace Lean.Expr

def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous

def getAppFnArgs (e : Expr) : Name × Array Expr :=
  withApp e λ e a => (e.constName, a)

/-- Converts a `Expr` of a list to a list of `Expr`s -/
partial def toListExpr (e : Expr) : List Expr := 
  match e.getAppFnArgs with 
    | (``List.nil, #[_]) => []
    | (``List.cons, #[_, x, xs]) => x :: toListExpr xs
    | _ => []

end Lean.Expr

namespace Array 

@[inline]
def concat {α : Type u} (ass : Array $ Array α) : Array α :=
  ass.foldl (init := empty) fun as a => as ++ a

end Array 
