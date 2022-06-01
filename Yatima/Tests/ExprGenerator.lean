import Yatima.Expr

def MAX_DEPTH : Nat := 10

structure Hole where
  id : Nat
  treeDepth : Nat
  -- 
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
  filledHoles : List (Hole × HExpr) -- KVMap for `Hole` and `HExpr`s 
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

-- generate 4-character long alpha names 
def randomName : IO String := do
  return String.mk [←randomAlpha, ←randomAlpha, ←randomAlpha, ←randomAlpha] 

-- not actually making a valid CID, just want something to fill in the holes
def randomCid : IO Cid := do
  let multiHash : Multihash := ⟨0, 0, .mk #[0xC0DE]⟩
  return ⟨← IO.rand 0 1, ← IO.rand 0 1, multiHash⟩

-- TODO: Need a way to generate random `UnivCIDs`
def randomSort : IO Yatima.Expr := do
  let univCid := ⟨.mk (← randomCid), .mk (← randomCid)⟩
  return .sort univCid

-- TODO: Need a way to generate random `ConstCid` (and `UnivCid`)s
def randomConst : IO Yatima.Expr := do
  let constCid := ⟨.mk (← randomCid), .mk (← randomCid)⟩
  return .const (← randomName) constCid []

def randomLit : IO Yatima.Expr := do
  let isNat ← IO.rand 0 1
  if isNat == 1 then return .lit $ .nat (← IO.rand 0 100) else return .lit $ .str (← randomName)

def randomVar (isBdd : Bool := false): IO Yatima.Expr := do
  let name ← randomName
  let freedom ← IO.rand 0 1 --
  if isBdd || freedom == 0 then 
    return .var (← randomName) (← IO.rand 0 2) else 
    return .var (← randomName) (← IO.rand 2 3)

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
        | .var varType => return (← randomVar) /- Can add in a Boolean parameter to ensure
                                                  the variables are all bounded -/

partial def run : ExprGen Yatima.Expr := do
  fillAllHoles
  let head := (← get).head
  assembleExprAux head

namespace Yatima.Expr

def toString : Yatima.Expr → String
  | var name idx => s!"v:{name}.{idx}"
  | sort _ => "Sort" -- Do this better
  | const name .. => s!"c:{name}"
  | app func body =>
    let funcString := func.toString
    let bodyString := body.toString
    s!"({funcString} {bodyString})"
  | lam _ _ type body =>
    let bodyString := body.toString
    s!"(λ. {bodyString})"
  | pi _ _ type body =>
    let bodyString := body.toString
    s!"(Π. {bodyString})"
  | letE _ type value body =>
    let valueString := value.toString
    let bodyString := body.toString
    s!"(let v=({valueString}) in {bodyString})" -- Do this better
  | lit literal =>
    match literal with
      | .nat num => s!"{num}"
      | .str str => str
  | lty _ => "" -- Not generating literal types yet
  | fix _ body => 
    let bodyString := body.toString
    s!"(μ.{bodyString})"

instance : ToString Expr := {
  toString := Expr.toString
}

end Yatima.Expr

def printRandomExpr : IO Unit := do
  let as ← run.run' init
  IO.println s!"{as}"

def printExamples : IO Unit := do
  for _ in List.range 5 do
    printRandomExpr

-- Absolutely cursed outputs:
--#eval printExamples
-- (λ. (μ.(μ.(let v=((μ.(μ.(Π. (μ.(λ. (rezB 9))))))) in (μ.(μ.(Π. (μ.(λ. (65 JtPB))))))))))
-- (((λ. (μ.(let v=((let v=((((μ.(let v=(23) in 17)) (μ.(let v=(WZbf) in HyQi))) ((μ.(let v=(sAjD) in 77)) (μ.(let v=(80) in VcZO))))) in (((μ.(let v=(27) in Qyzm)) (μ.(let v=(59) in tjLz))) ((μ.(let v=(39) in 84)) (μ.(let v=(48) in 89)))))) in (let v=((((μ.(let v=(PAno) in 85)) (μ.(let v=(14) in 99))) ((μ.(let v=(XaIN) in 61)) (μ.(let v=(34) in DlWT))))) in (((μ.(let v=(49) in AGIQ)) (μ.(let v=(61) in nVvV))) ((μ.(let v=(dMPj) in 64)) (μ.(let v=(1) in 21)))))))) (λ. (μ.(let v=((let v=((((μ.(let v=(39) in oRBH)) (μ.(let v=(59) in AcPx))) ((μ.(let v=(95) in 41)) (μ.(let v=(73) in ewSA))))) in (((μ.(let v=(15) in 38)) (μ.(let v=(ShdC) in WDMR))) ((μ.(let v=(63) in 74)) (μ.(let v=(92) in jdzh)))))) in (let v=((((μ.(let v=(WaFI) in 26)) (μ.(let v=(1) in Fmie))) ((μ.(let v=(94) in eRWj)) (μ.(let v=(NGow) in YTFT))))) in (((μ.(let v=(IqWc) in JJjR)) (μ.(let v=(3) in AKIM))) ((μ.(let v=(23) in 78)) (μ.(let v=(92) in dYlL))))))))) ((λ. (μ.(let v=((let v=((((μ.(let v=(35) in 100)) (μ.(let v=(2) in oreH))) ((μ.(let v=(77) in Uolu)) (μ.(let v=(xsDk) in FIDc))))) in (((μ.(let v=(34) in 85)) (μ.(let v=(WBBz) in pJgU))) ((μ.(let v=(51) in ZKkA)) (μ.(let v=(mfhm) in 8)))))) in (let v=((((μ.(let v=(RRoi) in qcGC)) (μ.(let v=(PJxm) in 51))) ((μ.(let v=(zAgz) in PILL)) (μ.(let v=(xykK) in 12))))) in (((μ.(let v=(79) in 20)) (μ.(let v=(QqQL) in 78))) ((μ.(let v=(OIvf) in pxNP)) (μ.(let v=(lsoR) in egEn)))))))) (λ. (μ.(let v=((let v=((((μ.(let v=(ZdXn) in 29)) (μ.(let v=(45) in 3))) ((μ.(let v=(NDvF) in 74)) (μ.(let v=(75) in VlWH))))) in (((μ.(let v=(42) in 32)) (μ.(let v=(9) in 51))) ((μ.(let v=(27) in 55)) (μ.(let v=(rjBh) in 9)))))) in (let v=((((μ.(let v=(kuzm) in 25)) (μ.(let v=(rgPl) in 73))) ((μ.(let v=(66) in 2)) (μ.(let v=(lClH) in 55))))) in (((μ.(let v=(wlPn) in 3)) (μ.(let v=(75) in EyrI))) ((μ.(let v=(94) in YHqS)) (μ.(let v=(Bwkv) in oXVH))))))))))
-- (μ.(λ. (let v=((μ.(μ.(let v=((μ.(((μ.v:qwjK.3) (μ.v:yPhM.2)) ((μ.v:tora.0) (μ.v:dWrQ.2))))) in (μ.(((μ.v:dHdV.0) (μ.v:qKty.2)) ((μ.v:BgFI.3) (μ.v:XQsb.2)))))))) in (μ.(μ.(let v=((μ.(((μ.v:Nbvu.0) (μ.v:hAWW.1)) ((μ.v:imSv.0) (μ.v:oUXa.0))))) in (μ.(((μ.v:HXsU.3) (μ.v:GxMP.3)) ((μ.v:MLFF.2) (μ.v:mBAK.2))))))))))
-- (Π. (λ. (((Π. (Π. (let v=((μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort)))) in (μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort)))))) (Π. (Π. (let v=((μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort)))) in (μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort))))))) ((Π. (Π. (let v=((μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort)))) in (μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort)))))) (Π. (Π. (let v=((μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort)))) in (μ.(let v=((let v=(Sort) in Sort)) in (let v=(Sort) in Sort))))))))))
-- (μ.((μ.(let v=((let v=((μ.(λ. ((let v=((v:Wkra.0 v:CdOu.3)) in (v:UjPj.2 v:CDPj.0)) (let v=((v:TxYo.3 v:bBUJ.1)) in (v:ylPF.2 v:GbEM.3)))))) in (μ.(λ. ((let v=((v:lJuU.3 v:jpdO.2)) in (v:jJUj.3 v:PsEn.3)) (let v=((v:TcDP.3 v:YtgJ.0)) in (v:hJlX.2 v:Uzsj.2))))))) in (let v=((μ.(λ. ((let v=((v:bALc.3 v:mmMx.3)) in (v:LVoL.0 v:nHOv.1)) (let v=((v:nouj.2 v:fyWR.2)) in (v:kZRw.2 v:ICrA.2)))))) in (μ.(λ. ((let v=((v:TLSg.0 v:UWjN.3)) in (v:aqkX.2 v:QBZO.0)) (let v=((v:tGNY.0 v:pckg.1)) in (v:lFFc.0 v:hpzE.2)))))))) (μ.(let v=((let v=((μ.(λ. ((let v=((v:iegu.1 v:IXGr.3)) in (v:OQqN.2 v:RheE.3)) (let v=((v:nKYQ.2 v:nmEh.3)) in (v:Dggk.2 v:MfcD.3)))))) in (μ.(λ. ((let v=((v:ndWQ.2 v:wQwf.2)) in (v:iUEZ.2 v:nwGr.2)) (let v=((v:IdhU.2 v:QPOa.3)) in (v:uxrm.3 v:sSqP.2))))))) in (let v=((μ.(λ. ((let v=((v:GjDj.3 v:DUtU.2)) in (v:DLKk.0 v:WOPI.2)) (let v=((v:RuZD.2 v:eUvS.1)) in (v:EtRh.2 v:mIMK.3)))))) in (μ.(λ. ((let v=((v:MBOO.2 v:CYUe.2)) in (v:ZFbk.2 v:Fxft.0)) (let v=((v:jaSY.3 v:mWDb.0)) in (v:BKHR.2 v:AkWQ.1))))))))))