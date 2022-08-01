import LSpec
import Yatima.Compiler.Compiler
import Yatima.Ipld.FromIpld
import YatimaStdLib.List

open Yatima LSpec

def getConstPairs (fileName : String) (consts : List Lean.Name) :
    IO $ Except String (List (Const × Const)) := do
  match ← Compiler.compile fileName with
  | .error msg => return .error (toString msg)
  | .ok state =>
    let store := state.store
    let convState ← do match FromIpld.convertStore store with
    | .ok state => pure state
    | .error msg => return .error s!"FromIpld.convertStore failed: {msg}"
    let mut pairList : List (Const × Const) := []
    let mut notFoundCompiled : List Lean.Name := []
    let mut notFoundConverted : List Lean.Name := []
    for const in consts do
      match state.cache.find? const with
      | none            => notFoundCompiled := const :: notFoundCompiled
      | some (cid, idx) =>
        let constCompiled := state.defns[idx]!
        match convState.const_cache.find? cid with
        | none     => notFoundConverted := const :: notFoundConverted
        | some idx =>
          let constConverted := convState.defns[idx]!
          pairList := (constCompiled, constConverted) :: pairList
    if notFoundCompiled.isEmpty && notFoundConverted.isEmpty then
      return .ok pairList
    else 
      if !notFoundCompiled.isEmpty then
        return .error s!"Not found: {", ".intercalate (notFoundCompiled.map toString)}"
      if !notFoundConverted.isEmpty then
        return .error s!"Not found: {", ".intercalate (notFoundConverted.map toString)}"
      return .error ""

def makeTests (pairList : List (Const × Const)) :
    TestSeq :=
  pairList.foldl (init := .done) fun tSeq (constCompiled, constConverted) =>
    tSeq ++ test s!"{constCompiled.name} compiled = {constConverted.name} converted" (constCompiled == constConverted)

def definitionsPair :=
  ("Fixtures/AnonCidGroups/Definitions.lean", [
    `A, `A',
    `B, `B',
    `C, `C',
    `E, `E',
    `F, `F',
    `G, `G',
    `H, `H',
    `I, `I']
  )

def partialDefinitionsPair :=
  ("Fixtures/AnonCidGroups/PartialDefinitions.lean",
    [`A, `C, `E, `F, `B, `G, `H, `I]) -- the bodies of partial definitions
                                          -- are ignored by Lean's kernel

def unsafeDefinitionsPair :=
  ("Fixtures/AnonCidGroups/UnsafeDefinitions.lean",
    [`A, `C, `E, `F, `B, `G, `H, `I])

def inductivesPair :=
  ("Fixtures/AnonCidGroups/Inductives.lean", [
    `BLA, `BLU,
    `BLA',
    `BLE, `BLE',
    `BLI, `BLI',
    `BLO, `BLO',
    `BLE'',
    `BLI'',
    `BLO'',
    `BLEH]
  )

def importPair :=
  ("Fixtures/AnonCidGroups/ToImport.lean", [`Nat, `MyNat, `MyOtherNat])

def allPairs : List (String × List Lean.Name) := [
  --definitionsPair,
  --partialDefinitionsPair,
  --unsafeDefinitionsPair,
  --inductivesPair,
  --importPair
]

def generateTestSeq (x : String × List Lean.Name) : IO TestSeq :=
  return withExceptOk s!"Compiles '{x.1}'" (← getConstPairs x.1 x.2)
    fun pairs => makeTests pairs

def main : IO UInt32 := do
  Compiler.setLibsPaths
  lspecEachIO allPairs generateTestSeq
