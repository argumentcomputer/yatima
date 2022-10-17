import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Termination/Prelude.lean"
    [/-extractIpldTests, extractIpldRoundtripTests,-/ extractPositiveTypecheckTests]
    false
  lspecIO tSeq
