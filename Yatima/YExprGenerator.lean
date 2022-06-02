import Yatima.Expr

def MAX_DEPTH : Nat := 30

structure Hole where
  id : Nat
  treeDepth : Nat
  -- Eventually may store the type signature of a Hole to generate type-correct Yatima expressions.
deriving Inhabited  

instance : BEq Hole where
  beq := fun h₁ h₂ => h₁.id == h₂.id

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
          | .letE .. => pure $ some 0 --TODO: Look at the wiki page and 
          | .fix body  => getBinderDepthAux hole body acc 

def getHoles (expr : HExpr) : ExprGen (List Hole) := do
  match expr with
    | .lam type body => return [type, body]
    | .app func input => return [func, input]
    | .pi  type body => return [type, body]
    | .letE type value body => return [type, value, body]
    | .fix body => return [body]
    | .leaf _ => return []

def genExpr (depth : Nat) (type : ExprType) : ExprGen HExpr := do
  match type with
    | .inl nodeType => match nodeType with
        | .app  => return .app (← genNewHole depth.succ) (← genNewHole depth.succ) 
        | .lam  => return .lam (← genNewHole depth.succ) (← genNewHole depth.succ) 
        | .pi   => return .pi (← genNewHole depth.succ) (← genNewHole depth.succ) 
        | .letE => return .letE (← genNewHole depth.succ)
                                (← genNewHole depth.succ)
                                (← genNewHole depth.succ)
        | .fix  => return .fix (← genNewHole depth.succ)
    | .inr leafType => return .leaf leafType

def fillHole (target : Hole) (type : ExprType) : ExprGen Unit := do
  let state ← get
  let expr ← genExpr (target.treeDepth) type
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

def getRandomType (isLeaf : Bool := False): IO ExprType := do
  if isLeaf then 
    let leafTypeNum ← IO.rand 0 3
    match leafTypeNum with
      | 0 => return Sum.inr .sort
      | 1 => return Sum.inr .const
      | 2 => return Sum.inr .lit
      | _ => 
        let isFree ← IO.rand 0 1
        return Sum.inr $ .var (if isFree == 1 then .free else .bdd)
  else
    let nodeTypeNum ← IO.rand 0 4
    match nodeTypeNum with
      | 0 => return Sum.inl .app
      | 1 => return Sum.inl .lam
      | 2 => return Sum.inl .pi
      | 3 => return Sum.inl .letE
      | _ => return Sum.inl .fix

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

def randomAlpha : IO Char := do
  let isUpper ← IO.rand 0 1
  if (isUpper == 1) then return .ofNat (← IO.rand 65 90) else return .ofNat (← IO.rand 97 122)

-- generate 3-character long alpha names 
def randomName : IO String := do
  return String.mk [←randomAlpha, ←randomAlpha, ←randomAlpha] 

-- TODO: Need a way to generate random `UnivCIDs`
def randomSort : IO Yatima.Expr := sorry

-- TODO: Need a way to generate random `ConstCid` (and `UnivCid`)s
def randomConst : IO Yatima.Expr := sorry

-- TODO: Just use randomName
def randomLit : IO Yatima.Expr := sorry

-- TODO: Same structure as before
def randomVar : IO Yatima.Expr := sorry

partial def assembleExprAux (head : Hole) : ExprGen Yatima.Expr := do
  let hExpr ← getValue? head
  match hExpr with
    | none => unreachable!
    | some expr => match expr with
      | .app funcHole inputHole           => 
        return .app (← assembleExprAux funcHole) (← assembleExprAux inputHole)
      | .lam typeHole bodyHole            => 
        return .lam (← randomName) default (← assembleExprAux typeHole) (← assembleExprAux bodyHole)
      | .pi typeHole bodyHole             => 
        return .pi (← randomName) default (← assembleExprAux typeHole) (← assembleExprAux bodyHole)
      | .letE typeHole valueHole bodyHole =>
        return .letE (← randomName) (← assembleExprAux typeHole) 
                                    (← assembleExprAux valueHole) 
                                    (← assembleExprAux bodyHole)
      | .fix bodyHole                     => 
        return .fix (← randomName) (← assembleExprAux bodyHole) 
      | .leaf leafType => match leafType with
        | .sort        => return (← randomSort)
        | .const       => return (← randomConst)
        | .lit         => return (← randomLit)
        | .var varType => return (← randomVar)

partial def run : ExprGen Yatima.Expr := do
  fillAllHoles
  let head := (← get).head
  assembleExprAux head

-- TODO: write a `ToString` instance to read the result (not super important)