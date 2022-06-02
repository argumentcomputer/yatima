import Yatima.Expr

def MAX_DEPTH : Nat := 30

structure Hole where
  id : Nat
  treeDepth : Nat
  -- Eventually may store the type signature of a Hole to generate type-correct Yatima expressions.
deriving Inhabited  

instance : BEq Hole where
  beq := fun h₁ h₂ => h₁.id == h₂.id

inductive VarType 
  | free
  | bdd

inductive LeafType | sort | const | lit | var : VarType → LeafType

/--
The type of **holed** Yatima expressions. Holes are basically less fancy Lean metavariables
-/
inductive HExpr
  | app  : Hole → Hole → HExpr
  | lam  : Hole → Hole → HExpr
  | pi   : Hole → Hole → HExpr
  | letE : Hole → Hole → Hole → HExpr
  | fix  : Hole → HExpr
  | leaf : LeafType → HExpr
deriving Inhabited

structure State where
  holes : List Hole
  filledHoles : List (Hole × HExpr) -- KVMap for `Hole`s and `HExpr` 
  head : Hole

def init : State := 
  let hole : Hole := ⟨0, 0⟩
{
  holes := [hole]
  filledHoles := []
  head := hole
}

abbrev ExprGen := StateT State IO

def isFilled (hole : Hole) : ExprGen Bool := do
  let keys := (← get).filledHoles.map (fun (h, _) => h.id)
  return keys.elem hole.id

def getIndex? (hole : Hole) : ExprGen (Option Nat) := do
  let keys := (← get).filledHoles.map (fun (h, _) => h)
  return keys.indexOf hole

def getValue? (hole : Hole) : ExprGen (Option HExpr) := do
  let n := (← getIndex? hole)
  match n with
    | none => return none
    | some n => 
      let pairs := (← get).filledHoles
      return some $ pairs.get! n |>.2

def getHoleIds : ExprGen (List Nat) := do
  let holes := (← get).holes
  let filledHoles := (← get).filledHoles.map Prod.fst
  return (filledHoles ++ holes).map Hole.id
  
def genNewHole (depth : Nat) : ExprGen Hole := do
  let takenIds ← getHoleIds
  match takenIds.maximum? with
    | none    => 
      IO.println "Does this ever happen?" -- I don't think this ever happens
      let newHole : Hole := ⟨0, depth⟩
      let state ← get
      let newState : State := {
        holes := newHole :: state.holes
        filledHoles := state.filledHoles
        head := state.head
      }
      return newHole
    | some id => 
      let newHole : Hole := ⟨id + 1, depth⟩
      let state ← get
      let newState : State := {
        holes := newHole :: state.holes
        filledHoles := state.filledHoles
        head := state.head
      }
      return newHole

def getNextHole : ExprGen (Option Hole) := do
  let holes := (← get).holes
  match holes with
    | []        => return none
    | hole :: _ => return some hole

partial def getBinderDepth (hole : Hole) : ExprGen Nat := do
  let head := (← get).head
  getBinderDepthAux hole head 0
  where getBinderDepthAux (hole : Hole) (head : Hole) (acc : Nat) : ExprGen Nat := do
    let expr? := (← getValue? head)
      match expr? with 
        | none => unreachable!
        | some expr => match expr with
          | .leaf _ => return acc
          | .lam type body  => if body == hole then return acc else getBinderDepthAux hole body (acc + 1)
          | .pi type body   => if body == hole then return acc else getBinderDepthAux hole body (acc + 1)
          | .app func input => if hole == func || hole == input then return acc else 
            let inFunc ← getBinderDepthAux hole func acc
            let inInput ← getBinderDepthAux hole input acc
            return min inFunc inInput
          | other => return 0 -- TODO: Keep working 

open Yatima