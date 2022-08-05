import LSpec
import Yatima.Datatypes.Cid
import Yatima.Compiler.Compiler
import Yatima.Ipld.FromIpld
import Yatima.Compiler.Printing

open LSpec Yatima Compiler FromIpld

def compileAndExtractTests (fixture : String)
  (extractors : List (CompileState → TestSeq) := []) (setPaths : Bool := true) :
    IO TestSeq := do
  if setPaths then setLibsPaths
  return withExceptOk s!"Compiles '{fixture}'" (← compile fixture true)
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
    Except String (Array (Array (Lean.Name × Ipld.ConstCid .Anon))) := Id.run do
  let mut notFound : Array Lean.Name := #[]
  let mut cidGroups : Array (Array (Lean.Name × Ipld.ConstCid .Anon)) := #[]
  for group in groups do
    let mut cidGroup : Array (Lean.Name × Ipld.ConstCid .Anon) := #[]
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

section IpldRoundtrip

/-
This section defines an extractor that validates that the Ipld conversion
roundtrips for every constant in the `CompileState.store`.
-/

def find? [BEq α] (as : List α) (f : α → Bool) : Option (Nat × α) := Id.run do
  for x in as.enum do
    if f x.2 then return some x
  return none

abbrev NatNatMap := Std.RBMap Nat Nat compare

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
  | e@(.sort _)
  | e@(.lit ..)
  | e@(.lty ..) => e
  | .const n i ls => .const n (map.find! i) ls
  | .app e₁ e₂ => .app (reindexExpr map e₁) (reindexExpr map e₂)
  | .lam n bi e₁ e₂ => .lam n bi (reindexExpr map e₁) (reindexExpr map e₂)
  | .pi n bi e₁ e₂ => .pi n bi (reindexExpr map e₁) (reindexExpr map e₂)
  | .letE n e₁ e₂ e₃ =>
    .letE n (reindexExpr map e₁) (reindexExpr map e₂) (reindexExpr map e₃)
  | .proj n e => .proj n (reindexExpr map e)

def reindexConst (map : NatNatMap) : Const → Const
  | .axiom x => .axiom { x with type := reindexExpr map x.type }
  | .theorem x => .theorem { x with
    type := reindexExpr map x.type, value := reindexExpr map x.value }
  | .inductive x => .inductive { x with type := reindexExpr map x.type }
  | .opaque x => .opaque { x with
    type := reindexExpr map x.type, value := reindexExpr map x.value }
  | .definition x => .definition { x with
    type := reindexExpr map x.type, value := reindexExpr map x.value }
  | .constructor x => .constructor { x with
    type := reindexExpr map x.type, rhs := reindexExpr map x.rhs }
  | .extRecursor x =>
    let rules := x.rules.map fun r => { r with rhs := reindexExpr map r.rhs }
    .extRecursor { x with
      type := reindexExpr map x.type, rules := rules }
  | .intRecursor x => .intRecursor { x with type := reindexExpr map x.type }
  | .quotient x => .quotient { x with type := reindexExpr map x.type }

def extractIpldRoundtripTests (stt : CompileState) : TestSeq :=
  withExceptOk "`FromIpld.extractConstArray` succeeds"
    (FromIpld.extractConstArray stt.store) fun defns =>
      let convStt := {stt with defns := defns}
      withExceptOk "Pairing succeeds" (pairConstants stt.defns defns) $
        fun (pairs, map) => pairs.foldl (init := .done) fun tSeq (c₁, c₂) =>
          let c₁Str := match Yatima.Compiler.PrintYatima.printConst c₁ stt  with
            | .ok r  => r
            | _      => "ERROR"
          let c₂Str := match Yatima.Compiler.PrintYatima.printConst c₂ convStt with
            | .ok r  => r
            | _      => "ERROR"
          let indent (s : String) := "\t" ++ ("\n\t".intercalate $ s.splitOn "\n")
          tSeq ++ test s!"{c₁.name} roundtrips\n{indent s!"{c₁Str}---\n{c₂Str}"}" ((reindexConst map c₁) == c₂)

end IpldRoundtrip
