import LSpec
import Lurk.Evaluation.Eval
import Yatima.Datatypes.Cid
import Yatima.Compiler.Compiler
import Yatima.Compiler.Printing
import Yatima.Converter.Converter
import Yatima.Typechecker.Typechecker
import Yatima.Transpiler.Transpiler
import Yatima.Ipld.FromIpld

open LSpec Yatima Compiler

def compileAndExtractTests (fixture : String)
  (extractors : List (CompileState → TestSeq) := []) (setPaths : Bool := true) :
    IO TestSeq := do
  if setPaths then setLibsPaths
  return withExceptOk s!"Compiles '{fixture}'" (← compile fixture)
    fun stt => (extractors.map fun extr => extr stt).foldl (init := .done)
      (· ++ ·)

section AnonCidGroups

/-
This section defines an extractor that consumes a list of groups of names and
creates tests that assert that:
1. Each pair of constants in the same group has the same anon CID
2. Each pair of constants in different groups has different anon CIDs
-/

def extractCidGroups (groups : List (List Lean.Name)) (stt : CompileState) :
    Except String (Array (Array (Lean.Name × IR.ConstCid .anon))) := Id.run do
  let mut notFound : Array Lean.Name := #[]
  let mut cidGroups : Array (Array (Lean.Name × IR.ConstCid .anon)) := #[]
  for group in groups do
    let mut cidGroup : Array (Lean.Name × IR.ConstCid .anon) := #[]
    for name in group do
      match stt.cache.find? name with
      | none          => notFound := notFound.push name
      | some (cid, _) => cidGroup := cidGroup.push (name, cid.anon)
    cidGroups := cidGroups.push cidGroup
  if notFound.isEmpty then
    return .ok cidGroups
  else
    return .error s!"Not found: {", ".intercalate (notFound.data.map toString)}"

def extractAnonCidGroupsTests (groups : List (List Lean.Name))
    (stt : CompileState) : TestSeq :=
  withExceptOk "All constants can be found" (extractCidGroups groups stt)
    fun anonCidGroups =>
      let cidEqTests := anonCidGroups.foldl (init := .done) fun tSeq cidGroup =>
        cidGroup.data.pairwise.foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ = {y.1}ₐₙₒₙ" (x.2 == y.2)
      anonCidGroups.data.pairwise.foldl (init := cidEqTests) fun tSeq (g, g') =>
        (g.data.cartesian g'.data).foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ ≠ {y.1}ₐₙₒₙ" (x.2 != y.2)

end AnonCidGroups

section Converting

open Converter

/-
This section defines an extractor that validates that the Ipld conversion
roundtrips for every constant in the `CompileState.store`.
-/

@[specialize]
def find? [BEq α] (as : List α) (f : α → Bool) : Option (Nat × α) := Id.run do
  for x in as.enum do
    if f x.2 then return some x
  return none

abbrev NatNatMap := Std.RBMap Nat Nat compare

open TC

instance : Ord Const where
  compare x y := compare x.name y.name

def pairConstants (x y : Array Const) :
    Except String ((Array (Const × Const)) × NatNatMap) := Id.run do
  let mut pairs : Array (Const × Const) := #[]
  let mut map : NatNatMap := default
  let mut notFound : Array Name := #[]
  for (i, c) in x.data.enum do
    match find? y.data fun c' => c.name == c'.name with
    | some (i', c') => pairs := pairs.push (c, c'); map := map.insert i i'
    | none          => notFound := notFound.push c.name
  if notFound.isEmpty then
    return .ok (pairs, map)
  else
    return .error s!"Not found: {", ".intercalate (notFound.data.map toString)}"

def reindexExpr (map : NatNatMap) : Expr → Expr
  | e@(.var ..)
  | e@(.sort _ _)
  | e@(.lit ..) => e
  | .const _ n i ls => .const default n (map.find! i) ls
  | .app _ e₁ e₂ => .app default (reindexExpr map e₁) (reindexExpr map e₂)
  | .lam _ n bi e₁ e₂ => .lam default n bi (reindexExpr map e₁) (reindexExpr map e₂)
  | .pi _ n bi e₁ e₂ => .pi default n bi (reindexExpr map e₁) (reindexExpr map e₂)
  | .letE _ n e₁ e₂ e₃ =>
    .letE default n (reindexExpr map e₁) (reindexExpr map e₂) (reindexExpr map e₃)
  | .proj _ n e => .proj default n (reindexExpr map e)

def reindexCtor (map : NatNatMap) (ctor : Constructor) : Constructor :=
  { ctor with type := reindexExpr map ctor.type, rhs := reindexExpr map ctor.rhs }

def reindexConst (map : NatNatMap) : Const → Const
  | .axiom x => .axiom { x with type := reindexExpr map x.type }
  | .theorem x => .theorem { x with
    type := reindexExpr map x.type, value := reindexExpr map x.value }
  | .inductive x => .inductive { x with
    type := reindexExpr map x.type,
    struct := x.struct.map (reindexCtor map) }
  | .opaque x => .opaque { x with
    type := reindexExpr map x.type, value := reindexExpr map x.value }
  | .definition x => .definition { x with
    type := reindexExpr map x.type,
    value := reindexExpr map x.value,
    all := x.all.map map.find! }
  | .constructor x => .constructor { x with
    type := reindexExpr map x.type, rhs := reindexExpr map x.rhs }
  | .extRecursor x =>
    let rules := x.rules.map fun r => { r with
      rhs := reindexExpr map r.rhs,
      ctor := reindexCtor map r.ctor }
    .extRecursor { x with
      type := reindexExpr map x.type, rules := rules }
  | .intRecursor x => .intRecursor { x with type := reindexExpr map x.type }
  | .quotient x => .quotient { x with type := reindexExpr map x.type }

def extractConverterTests (stt : CompileState) : TestSeq :=
  withExceptOk "`extractPureStore` succeeds"
    (extractPureStore stt.irStore) fun pStore =>
      withExceptOk "Pairing succeeds" (pairConstants stt.tcStore.consts pStore.consts) $
        fun (pairs, map) => pairs.foldl (init := .done) fun tSeq (c₁, c₂) =>
          tSeq ++ test s!"{c₁.name} ({c₁.ctorName}) roundtrips" (reindexConst map c₁ == c₂)

end Converting

section Typechecking

open Typechecker

/-
Here we define the following extractors:
* `extractPositiveTypecheckTests` asserts that our typechecker doesn't have
false negatives by requiring that everything that typechecks in Lean 4 should
also be accepted by our implementation
-/

def typecheckConstM (name : Name) : TypecheckM Unit := do
  ((← read).store.consts.toList.enum.filter (fun (_, const) => const.name == name)).forM fun (i, const) => checkConst const i

def typecheckConst (store : TC.Store) (name : Name) : Except String Unit :=
  match TypecheckM.run (.init store) (.init store) (typecheckConstM name) with
  | .ok u => .ok u
  | .error err => throw $ toString err

inductive FoundConstFailure (constName : String) : Prop

instance : Testable (FoundConstFailure constName) :=
  .isFailure $ .some s!"Could not find constant {constName}"

def extractPositiveTypecheckTests (stt : CompileState) : TestSeq :=
  stt.tcStore.consts.foldl (init := .done) fun tSeq const =>
    tSeq ++ withExceptOk s!"{const.name} ({const.ctorName}) typechecks"
      (typecheckConst stt.tcStore const.name) fun _ => .done

end Typechecking

section Transpilation

open Transpiler Lurk Evaluation

instance [BEq α] [BEq β] : BEq (Except α β) where 
  beq x y := match x, y with 
    | .ok x, .ok y => x == y 
    | .error x, .error y => x == y
    | _, _ => false

def extractTranspilationTests (expect : _root_.List (Lean.Name × Option Lurk.Syntax.Expr))
    (stt : CompileState) : TestSeq :=
  expect.foldl (init := .done) fun tSeq (root, expected) =>
    withExceptOk "Transpilation succeeds" (transpile stt.irStore root) fun expr =>
      let val := eval expr
      match expected with
        | some expected =>
          let exVal := eval expected
          tSeq ++ test s!"Evaluation of {root} yields {val}" (val == exVal)
        | none => tSeq

end Transpilation

section Ipld

def findDiff [BEq α] (as bs : List α) : Option (Nat × α × α) :=
  let rec go (as bs : List α ) (idx : Nat) : Option (Nat × α × α) :=
    match as, bs with
    | a :: as, b :: bs => if a == b then go as bs idx.succ else .some (idx, a, b)
    | _, _ => .none
  go as bs 0

def extractIpldTests (stt : CompileState) : TestSeq :=
  let store := stt.irStore
  let ipld := Ipld.storeToIpld stt.ipldStore
  withOptionSome "Ipld deserialization succeeds" (Ipld.storeFromIpld ipld)
    fun store' => 
      dbg_trace "THE DIFF"
      dbg_trace "========"
      dbg_trace Repr.reprPrec (findDiff (store.exprAnon.toList) (store'.exprAnon.toList)) 3
      dbg_trace "========"
      dbg_trace "END OF DIFF"
      test "IPLD DeSer roundtrips" (store.exprAnon.toList == store'.exprAnon.toList)

end Ipld
