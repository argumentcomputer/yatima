import Yatima.Ipld.Keccak
import Yatima.Ipld.Cid
import Yatima.Expr
import Yatima.Univ
import Yatima.Env
import Yatima.Cid
import Yatima.Const

import Lean

namespace Lean.Yatima.Compiler

abbrev ConstMap := Lean.SMap Lean.Name Yatima.Const

structure Context where
  env      : Lean.Environment
  constMap : Lean.ConstMap := {}

abbrev ConvM := ReaderT Context $ StateT ConstMap Id

instance : Monad ConvM :=
  let i := inferInstanceAs (Monad ConvM)
  { pure := i.pure, bind := i.bind }

-- As it stands, it is using Keccak256. Should be parametrized on hash functions later
def nameToCid (nam : Lean.Name) : Cid :=
  -- Should we use `Name.hash` or our own encoding of names?
  let digest := Keccak.keccak256 $ ByteArray.pushUInt64LE ByteArray.empty nam.hash
  -- TODO: Correct the following 4 values
  let size := 0
  let code := 0
  let version := 0
  let codec := 0
  let multihash := Multihash.mk size code digest
  Cid.mk version codec multihash

def leanExprToCid (e : Lean.Expr) : Cid := panic! "TODO"
def inductiveToCid (induct : InductiveVal) : Cid := panic! "TODO"
def combineCid (a : Cid) (b : Cid) : Cid := panic! "TODO"

def inductiveIsUnitLike (ctors : List Lean.Name) : ConvM Bool :=
  match ctors with
  | [ctor] => do
    match Lean.Environment.find? (← read).env ctor with
    | some info =>
      match info with
      | Lean.ConstantInfo.ctorInfo cval => pure (cval.numFields != 0)
      | _ => pure false
    | none => pure false
  | _ => pure false

def toYatimaLevel (levelParams : List Lean.Name) (lvl : Lean.Level) : Yatima.Univ :=
  match lvl with
  | Lean.Level.zero _ => Yatima.Univ.zero
  | Lean.Level.succ n _ => Yatima.Univ.succ (toYatimaLevel levelParams n)
  | Lean.Level.max a b _ => Yatima.Univ.max (toYatimaLevel levelParams a) (toYatimaLevel levelParams b)
  | Lean.Level.imax a b _ => Yatima.Univ.imax (toYatimaLevel levelParams a) (toYatimaLevel levelParams b)
  | Lean.Level.param nam _ =>
    match levelParams.indexOf nam with
    | some n => Yatima.Univ.param (Yatima.Name.mk nam.toString) n
    | none   => panic! s!"'{nam}' not found in '{levelParams}'"
  | Lean.Level.mvar _ _ => panic! "Unfilled level metavariable"

--mutual
--
--  partial def toYatimaRecursorRule (rules : Lean.RecursorRule) :
--      ConvM Yatima.RecRule := do
--    let cid := default -- TODO
--    let rhs ← toYatimaExpr rules.rhs []
--    return Yatima.RecRule.mk cid rules.nfields rhs
--
--  partial def toYatimaConstMap (nam : Lean.Name) : ConvM ConstMap := do
--    let insertConst := fun nam const => do
--      let _ ← toYatimaConst nam const
--      pure default
--    Lean.SMap.forM (← read).constMap insertConst
--    get
--
--  partial def toYatimaConst (nam : Lean.Name) (constInfo : Lean.ConstantInfo) :
--      ConvM Yatima.Const := do
--    let YatimaMap ← get
--    match YatimaMap.find?' nam with
--    | some const => pure const
--    | none => do
--      let const ← match constInfo with
--      | .axiomInfo struct => do
--        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
--        let level := struct.levelParams.length
--        let type ← toYatimaExpr struct.type struct.levelParams
--        pure $ Yatima.Const.axiomC cid level type
--      | .thmInfo struct => do
--        let level := struct.levelParams.length
--        let value ← toYatimaExpr struct.value struct.levelParams
--        let type ← toYatimaExpr struct.type struct.levelParams
--        pure $ Yatima.Const.theoremC level value type
--      | .opaqueInfo struct => do
--        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
--        let level := struct.levelParams.length
--        let value ← toYatimaExpr struct.value struct.levelParams
--        let type ← toYatimaExpr struct.type struct.levelParams
--        let is_unsafe := struct.isUnsafe
--        pure $ Yatima.Const.opaque cid level value type is_unsafe
--      | .defnInfo struct => do
--        let cid := combineCid (nameToCid struct.name) (leanExprToCid struct.type)
--        let level := struct.levelParams.length
--        let value ← toYatimaExpr struct.value struct.levelParams
--        let type ← toYatimaExpr struct.type struct.levelParams
--        let safety := struct.safety
--        pure $ Yatima.Const.defn cid level value type safety
--      | .ctorInfo struct => do
--        let cid := default -- TODO
--        let level := struct.levelParams.length
--        let type ← toYatimaExpr struct.type struct.levelParams
--        let ctor_idx := struct.cidx
--        let num_params := struct.numParams
--        let num_fields := struct.numFields
--        let is_unsafe := struct.isUnsafe
--        pure $ Yatima.Const.ctor cid level type ctor_idx num_params num_fields is_unsafe
--      | .inductInfo struct => do
--        let cid := inductiveToCid struct
--        let level := struct.levelParams.length
--        let type ← toYatimaExpr struct.type struct.levelParams
--        let num_params := struct.numParams
--        let num_indices := struct.numIndices
--        let is_unit ← inductiveIsUnitLike struct.ctors
--        let is_rec := struct.isRec
--        let is_unsafe := struct.isUnsafe
--        let is_reflexive := struct.isReflexive
--        let is_nested := struct.isNested
--        pure $ Yatima.Const.induct cid level type
--          num_params num_indices is_unit is_rec is_unsafe is_reflexive is_nested
--      | .recInfo struct => do
--        let cid := default -- TODO
--        let level := struct.levelParams.length
--        let type ← toYatimaExpr struct.type struct.levelParams
--        let num_params := struct.numParams
--        let num_indices := struct.numIndices
--        let num_motives := struct.numMotives
--        let num_minors := struct.numMinors
--        let rules ← List.mapM toYatimaRecursorRule struct.rules
--        let k := struct.k
--        let is_unsafe := struct.isUnsafe
--        pure $ Yatima.Const.recursor cid level type
--          num_params num_indices num_motives num_minors rules k is_unsafe
--      | .quotInfo struct => do
--        let level := struct.levelParams.length
--        let type ← toYatimaExpr struct.type struct.levelParams
--        let kind := struct.kind
--        pure $ Yatima.Const.quotient level type kind
--      modifyGet (fun YatimaMap => (const, Lean.SMap.insert' YatimaMap nam const))
--
--  partial def toYatimaExpr (lean : Lean.Expr) (levelParams : List Lean.Name) :
--      ConvM Yatima.Expr :=
--    match lean with
--    | Lean.Expr.bvar idx _ => return Yatima.Expr.var idx
--    | Lean.Expr.sort lvl _ => return Yatima.Expr.sort (toYatimaLevel levelParams lvl)
--    | Lean.Expr.const nam lvls _ => do
--      match (← read).constMap.find?' nam with
--      | some const =>
--        let const ← toYatimaConst nam const
--        return Yatima.Expr.const const (List.map (toYatimaLevel levelParams) lvls)
--      | none => panic! "Unknown constant"
--    | Lean.Expr.app fnc arg _ => do
--      let fnc ← toYatimaExpr fnc levelParams
--      let arg ← toYatimaExpr arg levelParams
--      return Yatima.Expr.app fnc arg
--    | Lean.Expr.lam _ bnd bod _ => do
--      let bnd ← toYatimaExpr bnd levelParams
--      let bod ← toYatimaExpr bod levelParams
--      return Yatima.Expr.lam bnd bod
--    | Lean.Expr.forallE _ dom img _ => do
--      let dom ← toYatimaExpr dom levelParams
--      let img ← toYatimaExpr img levelParams
--      return Yatima.Expr.pi dom img
--    | Lean.Expr.letE _ typ exp bod _ => do
--      let typ ← toYatimaExpr typ levelParams
--      let exp ← toYatimaExpr exp levelParams
--      let bod ← toYatimaExpr bod levelParams
--      return Yatima.Expr.letE typ exp bod
--    | Lean.Expr.lit lit _ => return Yatima.Expr.lit lit
--    | Lean.Expr.mdata _ e _ => toYatimaExpr e levelParams
--    | Lean.Expr.proj .. => panic! "Projections TODO"
--    | Lean.Expr.fvar .. => panic! "Unbound variable"
--    | Lean.Expr.mvar .. => panic! "Unfilled metavariable"
--
--end
