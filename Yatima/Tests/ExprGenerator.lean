import Yatima.Expr
import Yatima.Cid
import Std.Data.HashMap

-- Not recommended going over 15 unless generation parameters are adjusted below
def MAX_DEPTH : Nat := 15 

def VARIABLE_PREFERENCE : Nat := 20

structure Hole where
  id : Nat
  treeDepth : Nat
  -- Add in UnivLevel information to help generate more sensible expressions
  /-
  Maybe store the type signature of a Hole to generate type-correct Yatima expressions? (need typechecker)
  -/
deriving Inhabited  

instance : BEq Hole where
  beq := fun h₁ h₂ => h₁.id == h₂.id
instance : Hashable Hole where
  hash := fun h₁ => hash h₁.id

inductive NodeType | app | lam | pi | letE | fix
inductive VarType  | free | bdd
inductive LeafType | sort | const | lit | var : VarType → LeafType

abbrev ExprType := NodeType ⊕ LeafType 

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
  unfilledHoles : List Hole
  filledHoles : Std.HashMap Hole HExpr -- KVMap for `Hole` and `HExpr`s
  maxHoleID : Nat
  head : Hole

def init : State := 
  let hole : Hole := ⟨0, 0⟩
{
  unfilledHoles := [hole]
  filledHoles := .empty
  maxHoleID := 0
  head := hole
}

abbrev ExprGen := StateM State

def isFilled (hole : Hole) : ExprGen Bool := do
  return (← get).filledHoles.contains hole

def getValue? (hole : Hole) : ExprGen (Option HExpr) := do
  return (← get).filledHoles.find? hole

def genNewHole (depth : Nat) : ExprGen Hole := do
  let state ← get
  let newHole : Hole := ⟨state.maxHoleID + 1, depth⟩
  let newState : State := {
    unfilledHoles := state.unfilledHoles.concat newHole
    filledHoles := state.filledHoles
    maxHoleID := state.maxHoleID + 1
    head := state.head
    }
  set newState
  return newHole

def getNextHole : ExprGen (Option Hole) := do
  match (← get).unfilledHoles with
    | []        => return none
    | hole :: _ => return some hole

/--
Given a `hole`, find the binder depth of 
-/
partial def getBinderDepth (hole : Hole) : ExprGen (Option Nat) := do
  let head := (← get).head
  getBinderDepthAux hole head 0
  where getBinderDepthAux (hole : Hole) (head : Hole) (acc : Nat) : ExprGen (Option Nat) := do
    if head == hole then pure acc else
      let expr? := (← getValue? head)
      match expr? with
        | none => return none
        | some expr => match expr with
          |.leaf _ => return none
          | .lam type body  => 
            getBinderDepthAux hole type acc <||> getBinderDepthAux hole body acc.succ
          | .pi type body   =>
            getBinderDepthAux hole type acc <||> getBinderDepthAux hole body acc.succ
          | .app func input => 
            getBinderDepthAux hole func acc <||> getBinderDepthAux hole input acc
          | .letE type value body => 
          getBinderDepthAux hole type acc  <||> 
          getBinderDepthAux hole value acc <||>
          getBinderDepthAux hole body acc.succ
          | .fix body  => getBinderDepthAux hole body acc 

def getHoles (expr : HExpr) : ExprGen (List Hole) := do
  match expr with
    | .lam type body => return [type, body]
    | .app func input => return [func, input]
    | .pi  type body => return [type, body]
    | .letE type value body => return [type, value, body]
    | .fix body => return [body]
    | .leaf _ => return []

def genHExpr (depth : Nat) (type : ExprType) : ExprGen HExpr := do
  match type with
    | .inl nodeType => match nodeType with
        | .app  => 
          let funcHole := (← genNewHole depth.succ)
          let bodyHole := (← genNewHole depth.succ)
          return .app funcHole bodyHole
        | .lam  => 
          let typeHole := (← genNewHole depth.succ)
          let bodyHole := (← genNewHole depth.succ)
          return .lam typeHole bodyHole
        | .pi   =>
          let typeHole := (← genNewHole depth.succ)
          let bodyHole := (← genNewHole depth.succ)
          return .pi typeHole bodyHole
        | .letE => 
          let typeHole  := (← genNewHole depth.succ)
          let valueHole := (← genNewHole depth.succ)
          let bodyHole  := (← genNewHole depth.succ)
          return .letE typeHole valueHole bodyHole
        | .fix  => 
          let bodyHole := (← genNewHole depth.succ)
          return .fix bodyHole
    | .inr leafType => return .leaf leafType

def fillHole (target : Hole) (type : ExprType) : ExprGen Unit := do
  let expr ← genHExpr (target.treeDepth) type
  let state ← get
  let minusTarget := state.unfilledHoles.erase target
  let newFilledHoles := state.filledHoles.insert target expr
  let newState : State := {
        unfilledHoles := minusTarget
        filledHoles := newFilledHoles
        maxHoleID := state.maxHoleID
        head := state.head
      }
  set newState

variable {gen : Type} [RandomGen gen]

def getRandomType (g : gen) (isLeaf : Bool := False) : ExprType × gen := 
  let (randLeaf, g) := randNat g 0 100
  let cutoff := 100 - VARIABLE_PREFERENCE -- NOTE: Adjust this `cutoff` to change leaf generation order
  if isLeaf || (randLeaf ≥ cutoff) then
    let (leafTypeNum, g) := randNat g 0 3
    match leafTypeNum with
      | 0 => (Sum.inr .sort, g)
      | 1 => (Sum.inr .const, g)
      | 2 => (Sum.inr .lit, g)
      | _ => 
        let (isFree, g) := randBool g
        (Sum.inr $ .var (if isFree then .free else .bdd), g)
  else
    let (nodeTypeNum, g) := randNat g 0 4
    match nodeTypeNum with
      | 0 => (Sum.inl .app, g)
      | 1 => (Sum.inl .lam, g)
      | 2 => (Sum.inl .pi, g)
      | 3 => (Sum.inl .letE, g)
      | _ => (Sum.inl .fix, g)

def fillNextHole (g : gen) : ExprGen gen := do
  match (← get).unfilledHoles with
    | [] => return g
    | h :: hs =>
      if h.treeDepth ≥ MAX_DEPTH then 
        let (exprType, g) := getRandomType (isLeaf := true) g
        fillHole h exprType
        return g
      else
        let (exprType, g) := getRandomType g
        fillHole h exprType
        return g

partial def fillAllHoles (g : gen) : ExprGen gen := do
  let state ← get
  match state.unfilledHoles with
    | [] => return g
    | _ =>
      let g ← fillNextHole g
      fillAllHoles g

def randomAlpha (g : gen) : Char × gen :=
  let (isUpper, g) := randBool g
  let (lo, hi) := if isUpper then (65, 90) else (97, 122)
  let (charNat, g) := randNat g lo hi
  (.ofNat charNat, g)

def someRandom {α : Type} (f : gen → α × gen) (n : Nat) (g : gen) : List α × gen := 
  let rec someRandomAux (n : Nat) (acc : List α) (g : gen) := match n with
    | 0       => (acc, g)
    | .succ n => 
      let (a, g) := f g
      someRandomAux n (a :: acc) g
  someRandomAux n [] g

def randName (g : gen) : String × gen := 
  let (cs, g) := someRandom randomAlpha 4 g
  (.mk cs, g)

-- not actually making a valid CID, just want something to fill in the holes
def randCid (g : gen) : Cid × gen :=
  let multiHash : Multihash := ⟨0, 0, .mk #[0xC0DE]⟩
  let (ver, g) := randNat g 0 1
  let (num, g) := randNat g 0 1
  (⟨ver, num, multiHash⟩, g)

def randSort (g : gen) : Yatima.Expr × gen :=
  let (anonCid, g) := randCid g
  let (metaCid, g) := randCid g
  let univCid := ⟨⟨anonCid⟩, ⟨metaCid⟩⟩
  (.sort univCid, g)

def randConst (g : gen) : Yatima.Expr × gen :=
  let (name, g) := randName g
  let (anonCid, g) := randCid g
  let (metaCid, g) := randCid g
  let constCid := ⟨.mk anonCid, .mk metaCid⟩
  (.const name constCid [], g)

def randLit (g : gen) : Yatima.Expr × gen :=
  let (isNat, g) := randBool g
  if isNat then 
    let (num, g) := randNat g 0 100
    (.lit $ .nat num, g) else
    let (str, g) := randName g
    (.lit $ .str str, g)

def randVar (depth : Option Nat) (g : gen) (isBdd : Bool := false): Yatima.Expr × gen :=
  let (name, g) := randName g
  match depth with
    | none => 
      let (idx, g) := randNat g 0 100
      (.var name idx, g)
    | some dep => 
      let (isBddR, g) := randBool g
      if isBdd || isBddR then
        let (idx, g) := randNat g 0 dep
        (.var name idx, g) else
        let (idx, g) := randNat g (dep + 1) 100
        (.var name idx, g)

partial def assembleExprAux (head : Hole) (g : gen) : ExprGen Yatima.Expr := do
  let hExpr ← getValue? head
  match hExpr with
    | none => unreachable!
    | some expr => match expr with
      | .app funcHole inputHole           => 
        let (g₁, g₂) := RandomGen.split g
        return .app (← assembleExprAux funcHole g₁) (← assembleExprAux inputHole g₂)
      | .lam typeHole bodyHole            =>
        let (name, g) := randName g
        let (g₁, g₂) := RandomGen.split g 
        return .lam name default (← assembleExprAux typeHole g₁) (← assembleExprAux bodyHole g₂)
      | .pi typeHole bodyHole             =>
        let (name, g) := randName g 
        let (g₁, g₂) := RandomGen.split g
        return .pi name default (← assembleExprAux typeHole g₁) (← assembleExprAux bodyHole g₂)
      | .letE typeHole valueHole bodyHole =>
        let (name, g) := randName g
        let (g₁, g₂) := RandomGen.split g
        let (g₂, g₃) := RandomGen.split g₂
        return .letE name (← assembleExprAux typeHole g₁) 
                          (← assembleExprAux valueHole g₂) 
                          (← assembleExprAux bodyHole g₃)
      | .fix bodyHole                     =>
        let (name, g) := randName g
        return .fix name (← assembleExprAux bodyHole g) 
      | .leaf leafType => match leafType with
        | .sort        => return randSort g  |>.1
        | .const       => return randConst g |>.1
        | .lit         => return randLit g   |>.1
        | .var varType => 
          let depth? ← getBinderDepth head
          return randVar depth? g |>.1

partial def run (g : gen) : ExprGen Yatima.Expr := do
  let g ← fillAllHoles g
  let head := (← get).head
  assembleExprAux head g

-- This should end up being the typeclass instance for `Arbitrary Yatima.Expr`
def arb (g : gen) : Yatima.Expr := (run g).run init |>.run |>.1

namespace Yatima.Expr

def toString : Yatima.Expr → String
  | var name idx => s!"v:{name}.{idx}"
  | sort _ => "Sort"
  | const name .. => s!"c:{name}"
  | app func body =>
    let funcString := func.toString
    let bodyString := body.toString
    s!"({funcString} {bodyString})"
  | lam _ _ type body =>
    let bodyString := body.toString
    let typeString := type.toString
    s!"(λ({typeString}). {bodyString})"
  | pi _ _ type body =>
    let bodyString := body.toString
    let typeString := type.toString
    s!"(Π({typeString}). {bodyString})"
  | letE _ type value body =>
    let valueString := value.toString
    let bodyString := body.toString
    let typeString := type.toString
    s!"(let v=({valueString}) : ({typeString}) in {bodyString})" 
  | lit literal =>
    match literal with
      | .nat num => s!"ln:{num}"
      | .str str => s!"ls:{str}"
  | lty _ => ""
  | fix _ body => 
    let bodyString := body.toString
    s!"(μ.{bodyString})"

instance : ToString Expr := {
  toString := Expr.toString
}

end Yatima.Expr

def printRandomExpr : IO Unit := do
  let time ← IO.monoNanosNow
  IO.setRandSeed time
  let g' ← IO.stdGenRef.get
  let ast := arb g'
  IO.println s!"{ast}"

def printExamples : IO Unit := do
  for _ in List.range 5 do
    printRandomExpr
