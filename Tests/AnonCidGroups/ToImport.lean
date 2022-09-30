import TestsUtils.CompileAndExtractTests

def defsExtractor := extractAnonCidGroupsTests
  [[`Nat, `MyNat, `MyOtherNat]]

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/AnonCidGroups/ToImport.lean"
    [extractIpldTests, defsExtractor, extractIpldRoundtripTests]
  lspecIO tSeq
