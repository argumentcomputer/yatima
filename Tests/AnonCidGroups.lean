import LSpec
import Yatima.Compiler.Compiler
import YatimaStdLib.List

open Yatima

def extractCidGroups (fileName : String) (groups : List (List Lean.Name)) :
    IO $ Except String (List (List (Lean.Name × Ipld.ConstCid .Anon))) := do
  match ← Compiler.compile fileName with
  | .error msg => return .error msg
  | .ok store =>
    let mut notFound : List Lean.Name := []
    let mut cidGroups : List (List (Lean.Name × Ipld.ConstCid .Anon)) := []
    for group in groups do
      let mut cidGroup : List (Lean.Name × Ipld.ConstCid .Anon) := []
      for name in group do
        match store.cache.find? name with
        | none          => notFound := name :: notFound
        | some (cid, _) => cidGroup := (name, cid.anon) :: cidGroup
      cidGroups := cidGroup.reverse :: cidGroups
    if notFound.isEmpty then
      return .ok cidGroups.reverse
    else
      return .error s!"Not found: {", ".intercalate (notFound.map toString)}"

def makeCidTests (cidGroups : List (List (Lean.Name × Ipld.ConstCid .Anon))) :
    TestSeq :=
  let cidEqTests := cidGroups.foldl (init := .done) fun tSeq cidGroup =>
    cidGroup.pairwise.foldl (init := tSeq) fun tSeq (x, y) =>
      tSeq ++ test s!"{x.1}ₐₙₒₙ = {y.1}ₐₙₒₙ" (x.2 == y.2)
  cidGroups.pairwise.foldl (init := cidEqTests) fun tSeq (g, g') =>
    (g.cartesian g').foldl (init := tSeq) fun tSeq (x, y) =>
      tSeq ++ test s!"{x.1}ₐₙₒₙ ≠ {y.1}ₐₙₒₙ" (x.2 != y.2)

def definitionsPair :=
  ("Fixtures/AnonCidGroups/Definitions.lean", [
    [`A, `A'],
    [`B, `B'],
    [`C, `C'],
    [`E, `E'],
    [`F, `F'],
    [`G, `G'],
    [`H, `H'],
    [`I, `I']]
  )

def partialDefinitionsPair :=
  ("Fixtures/AnonCidGroups/PartialDefinitions.lean",
    [[`A, `C, `E, `F, `B, `G, `H], [`I]]) -- the bodies of partial definitions
                                          -- are ignored by Lean's kernel

def unsafeDefinitionsPair :=
  ("Fixtures/AnonCidGroups/UnsafeDefinitions.lean",
    [[`A, `C, `E, `F], [`B], [`G, `H], [`I]])

def inductivesPair :=
  ("Fixtures/AnonCidGroups/Inductives.lean", [
    [`BLA, `BLU],
    [`BLA'],
    [`BLE, `BLE'],
    [`BLI, `BLI'],
    [`BLO, `BLO'],
    [`BLE''],
    [`BLI''],
    [`BLO''],
    [`BLEH]]
  )

def importPair :=
  ("Fixtures/AnonCidGroups/ToImport.lean", [[`Nat, `MyNat, `MyOtherNat]])

def allPairs := [
  definitionsPair,
  partialDefinitionsPair,
  unsafeDefinitionsPair,
  inductivesPair,
  importPair]

def generateTestSeq (x : String × List (List Lean.Name)) : IO TestSeq :=
  return withExceptOk s!"Compiles '{x.1}'" (← extractCidGroups x.1 x.2)
    fun cidGroups => makeCidTests cidGroups

def main : IO UInt32 := do
  Compiler.setLibsPaths
  lspecEachWith allPairs generateTestSeq
