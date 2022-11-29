import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Typechecker/Negative.lean"
    [extractPositiveTypecheckTests, extractNegativeTypecheckTests 10]
  lspecIO tSeq