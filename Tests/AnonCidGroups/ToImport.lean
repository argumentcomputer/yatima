import TestsUtils.ContAddrAndExtractTests

def defsExtractor := extractAnonCidGroupsTests
  [[`Nat, `MyNat, `MyOtherNat]]

open LSpec in
def main := do
  let tSeq ← contAddrAndExtractTests
    "Fixtures/AnonCidGroups/ToImport.lean"
    [defsExtractor, extractIpldTests, extractExtractorTests]
  lspecIO tSeq
