import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Termination/Prelude.lean"
    [ --extractIpldRoundtripTests,
      extractPositiveTypecheckTests (.some [`test])]
    false
  lspecIO tSeq
