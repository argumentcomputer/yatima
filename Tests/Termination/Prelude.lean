import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests'
    #["Fixtures/Termination/Init/Prelude.lean", "Fixtures/Termination/Init/Coe.lean", "Fixtures/Termination/Init/Notation.lean", "Fixtures/Termination/Init/Tactics.lean", "Fixtures/Termination/Init/SizeOf.lean"]
    [/-extractIpldTests, extractConverterTests,-/ extractPositiveTypecheckTests]
  lspecIO tSeq
