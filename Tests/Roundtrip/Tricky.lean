import TestsUtils.ContAddrAndExtractTests

open LSpec in
def main := do
  let tSeq ← contAddrAndExtractTests
    "Fixtures/Roundtrip/Tricky.lean"
    [extractIpldTests, extractExtractorTests]
  lspecIO tSeq
