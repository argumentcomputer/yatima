import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Termination/Prelude.lean"
    [ --extractIpldRoundtripTests,
      extractPositiveTypecheckTests (.some [`eq_of_heq])]
    false
  lspecIO tSeq
