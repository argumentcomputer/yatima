import LSpec
import Yatima.Datatypes.Cid
import Yatima.Compiler.Compiler
import Yatima.Ipld.FromIpld

open LSpec Yatima Compiler FromIpld

def compileAndExtractTests (fixture : String)
  (extractors : List (CompileState → TestSeq)) (setPaths : Bool := true) :
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

def pairConstants (x y : Array Const) :
    Except String (Array (Const × Const)) := Id.run do
  let mut pairs : Array (Const × Const) := #[]
  let mut notFound : Array Name := #[]
  for c in x do
    match y.find? fun c' => c.name == c'.name with
    | some c' => pairs := pairs.push (c, c')
    | none => notFound := notFound.push c.name
  if notFound.isEmpty then
    return .ok pairs
  else
    return .error s!"Not found: {", ".intercalate (notFound.data.map toString)}"

def extractIpldRoundtripTests (stt : CompileState) : TestSeq :=
  withExceptOk "`FromIpld.extractConstArray` succeeds"
    (FromIpld.extractConstArray stt.store) fun defns =>
      withExceptOk "Pairing succeeds" (pairConstants stt.defns defns) $
        Array.foldl (init := .done) fun tSeq (c₁, c₂) =>
          tSeq ++ test s!"{c₁.name} roundtrips" (c₁ == c₂)

end IpldRoundtrip
