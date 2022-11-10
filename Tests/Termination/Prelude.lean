import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Termination/Prelude.lean"
    [extractLurkDataTests/-, extractConverterTests, extractPositiveTypecheckTests-/]
    false
  lspecIO tSeq
