import LSpec
import Yatima.Compiler.Frontend

-- move to std
def List.pairwise : List α → List (α × α)
  | [ ]
  | [_] => []
  | x :: y :: zs => ((y :: zs).map fun k => (x, k)) ++ (y :: zs).pairwise

-- move to std
def List.cartesian (as : List α) (bs : List β) : List (α × β) :=
  as.foldl (init := []) fun acc a => acc ++ bs.map fun b => (a, b)

-- move to lspec
def TestSeq.append : TestSeq → TestSeq → TestSeq
  | done, t => t
  | more d p i n, t' => more d p i $ n.append t'

-- move to lspec
instance : Append TestSeq where
  append := TestSeq.append

-- move to lspec
def withSuccess (descr : String) :
    Except String α → (α → TestSeq) → TestSeq
  | .error msg, _ => test s!"{descr}\n    {msg}" false
  | .ok    a,   f => test descr true $ f a

open Yatima

def extractCidGroups (fileName : String) (groups : List (List Lean.Name)) :
    IO $ Except String (List (List (Lean.Name × ConstAnonCid))) := do
  match ← Compiler.runFrontend fileName with
  | .error msg => return .error msg
  | .ok store =>
    let mut notFound : List Lean.Name := []
    let mut cidGroups : List (List (Lean.Name × ConstAnonCid)) := []
    for group in groups do
      let mut cidGroup : List (Lean.Name × ConstAnonCid) := []
      for name in group do
        match store.cache.find? name with
        | none          => notFound := name :: notFound
        | some (cid, _) => cidGroup := (name, cid.anon) :: cidGroup
      cidGroups := cidGroup :: cidGroups
    if notFound.isEmpty then
      return .ok cidGroups
    else
      return .error s!"Not found: {", ".intercalate notFound}"

def makeCidTests (cidGroups : List (List (Lean.Name × ConstAnonCid))) :
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
  return withSuccess s!"Compiles '{x.1}'" (← extractCidGroups x.1 x.2)
    fun cidGroups => makeCidTests cidGroups

def main : IO UInt32 := do
  let testDefinitions ← generateTestSeq definitionsTests
  let testInductives  ← generateTestSeq inductivesTests
  lspecIO do
    testDefinitions
    testInductives
