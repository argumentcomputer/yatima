import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Termination/NastyInductives.lean"
    -- [extractIpldRoundtripTests, extractPositiveTypecheckTests]
    [extractIpldTests]
    false
  lspecIO tSeq
