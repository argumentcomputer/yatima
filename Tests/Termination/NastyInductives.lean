import TestsUtils.ContAddrAndExtractTests

open LSpec in
def main := do
  let tSeq ← contAddrAndExtractTests
    "Fixtures/Termination/NastyInductives.lean"
    [extractIpldTests, extractExtractorTests]
    false
  lspecIO tSeq
