import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Roundtrip/Tricky.lean"
    [extractIpldRoundtripTests]
  lspecIO tSeq
