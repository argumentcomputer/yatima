import Yatima.Ipld.Keccak
import Yatima.Ipld.Cid
import Yatima.YTypes

open Lean

abbrev YConstMap := SMap Name YConst

structure Context where
  env      : Environment
  constMap : ConstMap := {}

abbrev ConvM := ReaderT Context $ StateT YConstMap Id
instance : Monad ConvM :=
  let i := inferInstanceAs (Monad ConvM)
  { pure := i.pure, bind := i.bind }

-- As it stands, it is using Keccak256. Should be parametrized on hash functions later
def nameToCid (nam : Name) : Cid :=
  -- Should we use `Name.hash` or our own encoding of names?
  let digest := Keccak.keccak256 $ ByteArray.pushUInt64LE ByteArray.empty nam.hash
  -- TODO: Correct the following 4 values
  let size := 0
  let code := 0
  let version := 0
  let codec := 0
  let multihash := Multihash.mk size code digest
  Cid.mk version codec multihash

def leanExprToCid (e : Expr) : Cid := panic! "TODO"
def inductiveToCid (induct : InductiveVal) : Cid := panic! "TODO"
def combineCid (a : Cid) (b : Cid) : Cid := panic! "TODO"

def inductiveIsUnitLike (ctors : List Name) : ConvM Bool :=
  match ctors with
  | [ctor] => do
    match Environment.find? (← read).env ctor with
    | some info =>
      match info with
      | ConstantInfo.ctorInfo cval => pure (cval.numFields != 0)
      | _ => pure false
    | none => pure false
  | _ => pure false

def leanLevelToYatima (levelParams : List Name) (lvl : Level) : Univ :=
  match lvl with
  | Level.zero _ => Univ.zero
  | Level.succ n _ => Univ.succ (leanLevelToYatima levelParams n)
  | Level.max a b _ => Univ.max (leanLevelToYatima levelParams a) (leanLevelToYatima levelParams b)
  | Level.imax a b _ => Univ.imax (leanLevelToYatima levelParams a) (leanLevelToYatima levelParams b)
  | Level.param nam _ =>
    match levelParams.indexOf nam with
    | some n => Univ.param n
    | none   => panic! s!"'{nam}' not found in '{levelParams}'"
  | Level.mvar _ _ => panic! "Unfilled level metavariable"

mutual

  partial def leanRuleToYatima (rules : RecursorRule) :
      ConvM YRecursorRule := do
    let cid := default -- TODO
    let rhs ← leanExprToYatima rules.rhs []
    return YRecursorRule.mk cid rules.nfields rhs

  partial def toYatimaConstMap (nam : Name) : ConvM YConstMap := do
    let insertConst := fun nam const => do
      let _ ← addConstInfo nam const
      pure default
    SMap.forM (← read).constMap insertConst
    get

  partial def addConstInfo (nam : Name) (constInfo : ConstantInfo) :
      ConvM YConst := do
    let YatimaMap ← get
    match YatimaMap.find?' nam with
    | some const => pure const
    | none => do
      let const ← match constInfo with
      | .axiomInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        let level := struct.levelParams.length
        let type ← leanExprToYatima struct.type struct.levelParams
        pure $ YConst.axiomC cid level type
      | .thmInfo struct => do
        let level := struct.levelParams.length
        let value ← leanExprToYatima struct.value struct.levelParams
        let type ← leanExprToYatima struct.type struct.levelParams
        pure $ YConst.theoremC level value type
      | .opaqueInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        let level := struct.levelParams.length
        let value ← leanExprToYatima struct.value struct.levelParams
        let type ← leanExprToYatima struct.type struct.levelParams
        let is_unsafe := struct.isUnsafe
        pure $ YConst.opaque cid level value type is_unsafe
      | .defnInfo struct => do
        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
        let level := struct.levelParams.length
        let value ← leanExprToYatima struct.value struct.levelParams
        let type ← leanExprToYatima struct.type struct.levelParams
        let safety := struct.safety
        pure $ YConst.defn cid level value type safety
      | .ctorInfo struct => do
        let cid := default -- TODO
        let level := struct.levelParams.length
        let type ← leanExprToYatima struct.type struct.levelParams
        let ctor_idx := struct.cidx
        let num_params := struct.numParams
        let num_fields := struct.numFields
        let is_unsafe := struct.isUnsafe
        pure $ YConst.ctor cid level type ctor_idx num_params num_fields is_unsafe
      | .inductInfo struct => do
        let cid := inductiveToCid struct
        let level := struct.levelParams.length
        let type ← leanExprToYatima struct.type struct.levelParams
        let num_params := struct.numParams
        let num_indices := struct.numIndices
        let is_unit ← inductiveIsUnitLike struct.ctors
        let is_rec := struct.isRec
        let is_unsafe := struct.isUnsafe
        let is_reflexive := struct.isReflexive
        let is_nested := struct.isNested
        pure $ YConst.induct cid level type
          num_params num_indices is_unit is_rec is_unsafe is_reflexive is_nested
      | .recInfo struct => do
        let cid := default -- TODO
        let level := struct.levelParams.length
        let type ← leanExprToYatima struct.type struct.levelParams
        let num_params := struct.numParams
        let num_indices := struct.numIndices
        let num_motives := struct.numMotives
        let num_minors := struct.numMinors
        let rules ← List.mapM leanRuleToYatima struct.rules
        let k := struct.k
        let is_unsafe := struct.isUnsafe
        pure $ YConst.recursor cid level type
          num_params num_indices num_motives num_minors rules k is_unsafe
      | .quotInfo struct => do
        let level := struct.levelParams.length
        let type ← leanExprToYatima struct.type struct.levelParams
        let kind := struct.kind
        pure $ YConst.quotient level type kind
      modifyGet (fun YatimaMap => (const, SMap.insert' YatimaMap nam const))

  partial def leanExprToYatima (lean : Expr) (levelParams : List Name) :
      ConvM YExpr :=
    match lean with
    | Expr.bvar idx _ => return YExpr.var idx
    | Expr.sort lvl _ => return YExpr.sort (leanLevelToYatima levelParams lvl)
    | Expr.const nam lvls _ => do
      match (← read).constMap.find?' nam with
      | some const =>
        let const ← addConstInfo nam const
        return YExpr.const const (List.map (leanLevelToYatima levelParams) lvls)
      | none => panic! "Unknown constant"
    | Expr.app fnc arg _ => do
      let fnc ← leanExprToYatima fnc levelParams
      let arg ← leanExprToYatima arg levelParams
      return YExpr.app fnc arg
    | Expr.lam _ bnd bod _ => do
      let bnd ← leanExprToYatima bnd levelParams
      let bod ← leanExprToYatima bod levelParams
      return YExpr.lam bnd bod
    | Expr.forallE _ dom img _ => do
      let dom ← leanExprToYatima dom levelParams
      let img ← leanExprToYatima img levelParams
      return YExpr.pi dom img
    | Expr.letE _ typ exp bod _ => do
      let typ ← leanExprToYatima typ levelParams
      let exp ← leanExprToYatima exp levelParams
      let bod ← leanExprToYatima bod levelParams
      return YExpr.letE typ exp bod
    | Expr.lit lit _ => return YExpr.lit lit
    | Expr.mdata _ e _ => leanExprToYatima e levelParams
    | Expr.proj .. => panic! "Projections TODO"
    | Expr.fvar .. => panic! "Unbound variable"
    | Expr.mvar .. => panic! "Unfilled metavariable"

end
