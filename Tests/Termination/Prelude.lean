import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Termination/Prelude.lean"
    [extractIpldTests, extractConverterTests, extractPositiveTypecheckTests]
    false
  lspecIO tSeq
