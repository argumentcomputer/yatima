import TestsUtils.CodeGenAndRunTests

open Lurk.Value

open LSpec in
def main := do
  let tSeq ← extractCodeGenTests
    ("Fixtures" / "CodeGeneration" / "Primitives.lean")
    [ ("natAdd",  300),
      ("natSub1", 98),
      ("natSub2", 0),
      ("natMul",  1024),
      ("natDiv1", 0),
      ("natDiv2", 33),
      ("natMod1", 1),
      ("natMod2", 37),
      ("natLe",   1),
      ("natBEqF", 0),
      ("natBEqT", 1),
      ("natEqF", 0),
      ("natEqT", 1),
      ("charA", 97),
      ("charOfNat", 97),
      ("charToNat", 97),
      ("list", ⦃(1 2 3 4 5 6)⦄),
      ("listMap", ⦃(2 3 4 5 6 7)⦄),
      ("listFoldl", 21),
      ("listBeq", 1),
      ("listEqF", 0),
      ("listEqT", 1),
      ("abcd", "abcd"),
      ("efg", "efg"),
      ("stringAppendInst", "abcdefg"),
      ("stringAppend", "abcdefg"),
      ("stringLength", 4),
      ("stringAppendLength", 7),
      ("stringBEqF", 0),
      ("stringBEqT", 1),
      ("stringEqF", 0),
      ("stringEqT", 1)]
  lspecIO tSeq
