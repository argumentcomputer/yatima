import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Roundtrip/Tricky.lean"
    [extractIpldTests, extractIpldRoundtripTests]
  lspecIO tSeq
