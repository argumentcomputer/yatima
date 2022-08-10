import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Termination/Extern.lean"
    [extractIpldRoundtripTests]
    false
  lspecIO tSeq
