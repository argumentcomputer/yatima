import TestsUtils.ContAddrAndExtractTests

open LSpec in
def main := do
  let tSeq ← contAddrAndExtractTests'
    #["Fixtures/Termination/Init/Prelude.lean",
      "Fixtures/Termination/Init/Coe.lean",
      "Fixtures/Termination/Init/Notation.lean",
      "Fixtures/Termination/Init/Tactics.lean",
      "Fixtures/Termination/Init/SizeOf.lean"]
    [
      extractIpldTests,
      extractExtractorTests,
      extractPositiveTypecheckTests]
  lspecIO tSeq
