import LSpec
import Yatima.Compiler.Frontend
import YatimaStdLib.List

open Yatima

def extractCidGroups (fileName : String) (groups : List (List Lean.Name)) :
    IO $ Except String (List (List (Lean.Name × Ipld.ConstCid .Anon))) := do
  match ← Compiler.runFrontend fileName with
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
      cidGroups := cidGroup :: cidGroups
    if notFound.isEmpty then
      return .ok cidGroups
    else
      return .error s!"Not found: {", ".intercalate notFound}"

def makeCidTests (cidGroups : List (List (Lean.Name × Ipld.ConstCid .Anon))) :
    TestSeq := Id.run do
  let mut tSeq : TestSeq := .done
  for cidGroup in cidGroups do
    for (x, y) in cidGroup.pairwise do
      tSeq := test s!"{x.1}ₐₙₒₙ = {y.1}ₐₙₒₙ" (x.2 == y.2) tSeq
  for (g, g') in cidGroups.pairwise do
    for (x, y) in g.cartesian g' do
      tSeq := test s!"{x.1}ₐₙₒₙ ≠ {y.1}ₐₙₒₙ" (x.2 != y.2) tSeq
  tSeq

def definitionsTests := ("Fixtures/Definitions.lean", [
  [`A, `C, `E, `F],
  [`B],
  [`G, `H]])

def inductivesTests := ("Fixtures/Inductives.lean", [
  [`BLA, `BLU],
  [`BLA'],
  [`BLE, `BLE'],
  [`BLI, `BLI'],
  [`BLO, `BLO'],
  [`BLE''],
  [`BLI''],
  [`BLO''],
  [`BLEH]])

def generateTestSeq (x : String × List (List Lean.Name)) : IO TestSeq :=
  return withExceptOk s!"Compiles '{x.1}'" (← extractCidGroups x.1 x.2)
    fun cidGroups => makeCidTests cidGroups

def main : IO UInt32 := do
  let testDefinitions ← generateTestSeq definitionsTests
  let testInductives  ← generateTestSeq inductivesTests
  lspecIO do
    testDefinitions
    testInductives
