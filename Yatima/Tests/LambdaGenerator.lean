/-
This file will define tests related to Yatima `Expr`s. In particular, to test `shift` and `subst` 
the aim is to write a generator for random `Expr` trees.

For now all it does is generate untyped lambda expressions, but this is just a PoC for the main goal.
-/
import Ipld.Utils

-- Basic inductive type for lambda expressions to test the expression generator before trying it on
-- full blown Yatima Exprs
inductive LExpr
  | var : Nat → LExpr
  | lam : LExpr → LExpr
  | app : LExpr → LExpr → LExpr
deriving Inhabited

namespace LExpr

/--
Shift the de Bruijn indices of variables above cutoff `cutoff` in expression `expr` by an increment` inc`

Implementation of `shift` and `subst` taken from _Types and Programming Languages_ by B. Pierce
-/
def shift (expr : LExpr) (inc : Nat) (cutoff : Nat) : LExpr :=
  let rec walk (cutoff : Nat) (expr : LExpr) := match expr with
    | var idx        => if idx < cutoff then var idx else var (idx + inc)
    | lam body       => lam $ walk (cutoff.succ) body
    | app func input => app (walk cutoff func) (walk cutoff input)
  walk cutoff expr

/--
Substitute the expression `term` into variables of depth `dep` in the expression `expr`
-/ 
def subst (expr term : LExpr) (dep : Nat) : LExpr := 
  let rec walk (acc : Nat) (expr : LExpr) := match expr with
    | var idx        => if idx == dep + acc then term.shift acc 0 else var idx
    | lam body       => lam $ walk (acc.succ) body
    | app func input => app (walk acc func) (walk acc input)
  walk 0 expr

end LExpr

section ExprGen

def MAX_DEPTH : Nat := 20

namespace ExprGen

structure Hole where
  id : Nat
  treeDepth : Nat
  -- Eventually may store the type signature of a Hole to generate type-correct Yatima expressions.
deriving Inhabited  

instance : BEq Hole where
  beq := fun h₁ h₂ => h₁.id == h₂.id

inductive varType 
  | free
  | bdd

inductive lExprType |V : varType → lExprType | L | A

inductive HLExpr 
  | var : varType → HLExpr
  | lam : Hole → HLExpr
  | app : Hole → Hole → HLExpr
deriving Inhabited

structure State where
  holes : List Hole
  filledHoles : List (Hole × HLExpr) -- KVMap for `Hole`s and `HLExpr` 
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

def getValue? (hole : Hole) : ExprGen (Option HLExpr) := do
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

partial def getBinderDepthAux (hole : Hole) (head : Hole) (acc : Nat) : ExprGen Nat := do
  let expr? := (← getValue? head)
  match expr? with 
    | none => unreachable!
    | some expr => match expr with
      | .var _ => return acc
      | .lam body => if body == hole then return acc else getBinderDepthAux hole body (acc + 1)
      | .app func input => if hole == func || hole == input then return acc else 
        let inFunc ← getBinderDepthAux hole func acc
        let inInput ← getBinderDepthAux hole input acc
        return min inFunc inInput

def getBinderDepth (hole : Hole) : ExprGen Nat := do
  let head := (← get).head
  getBinderDepthAux hole head 0

def getHoles (expr : HLExpr) : ExprGen (List Hole) := do
  match expr with
    | .var _          => return []
    | .lam body       => return [body]
    | .app func input => return [func, input]

def genHLExpr (depth : Nat) (type : lExprType) : ExprGen HLExpr := do
  match type with
    | .V idx => return .var idx
    | .L => 
      let bodyHole := (← genNewHole $ (depth + 1))
      return .lam bodyHole
    | .A =>
      let funcHole := (← genNewHole $ (depth + 1))
      let inputHole := (← genNewHole $ (depth + 1))
      return .app funcHole inputHole

def fillHole (target : Hole) (type : lExprType) : ExprGen Unit := do
  let state ← get
  let expr ← genHLExpr (target.treeDepth) type
  let newHoles' := state.holes.erase target
  let newHoles :=  newHoles' ++ (← getHoles expr)
  let idx ← getIndex? target
  match idx with
    | none    => 
      let newFilledHoles := (target, expr) :: state.filledHoles
      let newState : State := {
        holes := newHoles
        filledHoles := newFilledHoles
        head := state.head
      }
      return (← set newState)
    | some id =>
      let droppedHole := state.filledHoles.drop id
      let newFilledHoles := (target, expr) :: state.filledHoles
      let newState : State := {
        holes := newHoles
        filledHoles := newFilledHoles
        head := state.head
      }
      return (← set newState)

def getRandomType (isVar : Bool := False): IO lExprType := do
  if isVar then 
      let isFree ← IO.rand 0 1
      match isFree with
        | 0 => return .V .free
        | _ => return .V .bdd
  else
    let numType ← IO.rand 0 2
    match numType with
      | 1 => return .L
      | 2 => return .A
      | _ => 
        let isFree ← IO.rand 0 1
        match isFree with
          | 0 => return .V .free
          | _ => return .V .bdd

def fillNextHole : ExprGen Unit := do
  let state ← get
  match state.holes with
    | [] => return ()
    | h :: hs =>
      if h.treeDepth ≥ MAX_DEPTH then 
        let exprType ← getRandomType true
        fillHole h exprType
      else
        let exprType ← getRandomType
        fillHole h exprType
      
partial def fillAllHoles : ExprGen Unit := do
  let state ← get
  match state.holes with
    | [] => return ()
    | _ =>
      fillNextHole
      fillAllHoles

partial def assembleLExprAux (head : Hole) : ExprGen LExpr := do
  let hExpr ← getValue? head
  match hExpr with
    | none => 
      let bDepth ← getBinderDepth head
      return .var (bDepth + (← IO.rand (bDepth + 1) 100))
    | some expr => match expr with
      | .var type               => 
      let bDepth ← getBinderDepth head
      match type with
        | .free => 
          return .var (bDepth + (← IO.rand (bDepth + 1) 100))
        | .bdd =>
          return .var (← IO.rand 0 bDepth)
      | .lam bodyHole           => return .lam (← assembleLExprAux bodyHole)
      | .app funcHole inputHole => return .app (← assembleLExprAux funcHole) (← assembleLExprAux inputHole)

partial def run : ExprGen LExpr := do
  fillAllHoles
  let head := (← get).head
  assembleLExprAux head

end ExprGen

end ExprGen

section Printer

def LExpr.toString : LExpr → String
  | var idx => s!"#{idx}"
  | lam body => 
    let bodyStr := body.toString
    s!"(λ. {bodyStr})"
  | app func input =>
    let funcStr := func.toString
    let inputStr := input.toString
    s!"({funcStr} {inputStr})"

instance : ToString LExpr := {
  toString := LExpr.toString
}

end Printer

open LExpr
open ExprGen

-- Main function!
def printRandomLExpr : IO Unit := do
  let as ← ExprGen.run.run' init
  IO.println s!"{as}"

def printExamples : IO Unit := do
  for _ in List.range 20 do
    printRandomLExpr

-- #eval printExamples
-- Random output:
-- ((λ. (λ. #84)) (λ. (λ. #52)))
-- (λ. #78)
-- (λ. (λ. #21))
-- (((#0 #0) (#0 #0)) ((#0 #0) (#0 #0)))
-- (#0 #0)
-- (λ. #8)
-- (λ. (λ. ((λ. (((λ. (λ. #95)) (λ. (λ. #37))) ((λ. (λ. #9)) (λ. (λ. #77))))) (λ. (((λ. (λ. #40)) (λ. (λ. #44))) ((λ. (λ. #83)) (λ. (λ. #57))))))))
-- (((λ. ((λ. (λ. ((#55 #56) (#57 #61)))) (λ. (λ. ((#7 #66) (#73 #59)))))) (λ. ((λ. (λ. ((#56 #7) (#27 #39)))) (λ. (λ. ((#52 #83) (#58 #23))))))) ((λ. ((λ. (λ. ((#60 #59) (#86 #83)))) (λ. (λ. ((#77 #83) (#28 #43)))))) (λ. ((λ. (λ. ((#21 #25) (#35 #74)))) (λ. (λ. ((#22 #11) (#82 #75))))))))
-- (#73 #55)
-- #0
-- (λ. (λ. ((λ. (λ. #2)) (λ. (λ. #1)))))
-- (((λ. (#4 #94)) (λ. (#34 #37))) ((λ. (#49 #5)) (λ. (#31 #12))))
-- (λ. #69)
-- (λ. #0)
-- (λ. (λ. #24))
-- #31
-- #0
-- (((λ. (λ. #74)) (λ. (λ. #60))) ((λ. (λ. #21)) (λ. (λ. #28))))
-- #3
-- (λ. ((λ. #1) (λ. #0)))