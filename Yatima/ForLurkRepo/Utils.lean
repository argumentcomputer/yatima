import Lean 
import Yatima.ForLurkRepo.AST

namespace Lurk

def mkNumLit (n : Nat) : Literal := 
  .num (Fin.ofNat n)

namespace Expr

def mkNum (n : Nat) : Expr := 
  .lit $ .num (Fin.ofNat n)

def isNum (e : Expr) : Bool := 
  match e with | .lit $ .num _ => true | _ => false
  
def eqNum (e : Expr) (n : Nat) : Bool := 
  match e with | .lit $ .num m => n == m | _ => false

def mkStr (s : String) : Expr := 
  .lit $ .str s

def isStr (e : Expr) : Bool := 
  match e with | .lit $ .str _ => true | _ => false

def eqStr (e : Expr) (s₁ : String) : Bool := 
  match e with | .lit $ .str s₂ => s₁ == s₂ | _ => false

def mkIfElses (ifThens : List (Expr × Expr)) (finalElse : Expr) : Expr := 
  match ifThens with 
  | [] => .lit .nil 
  | [(cond, body)] => .ifE cond body finalElse
  | (cond, body) :: es => .ifE cond body (mkIfElses es finalElse)

/-- Replace all occurrences of `target` in `e` with `replacment`.-/
partial def replace (e : Expr) (target : Expr) (replacement : Expr) : Expr :=
  if e == target then 
    replacement 
  else match e with 
    | .lit _ => e
    | .ifE test con alt => 
      let test := replace test target replacement
      let con := replace con target replacement
      let alt := replace alt target replacement
      .ifE test con alt
    | .lam formals body => 
      let body := replace body target replacement
      .lam formals body
    | .letE binds body => 
      let binds := binds.map fun (n, e) => (n, replace e target replacement)
      let body := replace body target replacement
      .letE binds body
    | .letRecE binds body => 
      let binds := binds.map fun (n, e) => (n, replace e target replacement)
      let body := replace body target replacement
      .letRecE binds body
    | .app fn args => 
      let fn := replace fn target replacement
      let args := args.map fun arg => replace arg target replacement
      .app fn args
    | .quote _ => e
    | .unaryOp _ _ => e
    | .binOp _ _ _ => e 
    | .emit e => .emit <| replace e target replacement 
    | .begin es => .begin <| es.map fun e => replace e target replacement
    | .currEnv => e
    | .eval e env? => 
      let e := replace e target replacement
      let env? := env?.map fun env => replace env target replacement
      .eval e env?

/-- Given pairs `(tgtᵢ, rplᵢ)`, replaces all occurences of `tgtᵢ` with `rplᵢ`.
  This is more efficient than `replace` since one does not have to traverse
  the `Expr` tree multiple times. We do not recursively call `replaceN` on 
  the newly replaced `rplᵢ` expressions. -/
partial def replaceN (e : Expr) (targets : List (Expr × Expr)) : Expr :=
  match targets.find? fun (tgt, _) => e == tgt with 
  | some (_, rpl) => rpl 
  | none => match e with 
    | .lit _ => e
    | .ifE test con alt => 
      let test := replaceN test targets
      let con := replaceN con targets
      let alt := replaceN alt targets
      .ifE test con alt
    | .lam formals body => 
      let body := replaceN body targets
      .lam formals body
    | .letE binds body => 
      let binds := binds.map fun (n, e) => (n, replaceN e targets)
      let body := replaceN body targets
      .letE binds body
    | .letRecE binds body => 
      let binds := binds.map fun (n, e) => (n, replaceN e targets)
      let body := replaceN body targets
      .letRecE binds body
    | .app fn args => 
      let fn := replaceN fn targets
      let args := args.map fun arg => replaceN arg targets
      .app fn args
    | .quote _ => e
    | .unaryOp _ _ => e
    | .binOp _ _ _ => e 
    | .emit e => .emit <| replaceN e targets 
    | .begin es => .begin <| es.map fun e => replaceN e targets
    | .currEnv => e
    | .eval e env? => 
      let e := replaceN e targets
      let env? := env?.map fun env => replaceN env targets
      .eval e env?

end Expr 
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