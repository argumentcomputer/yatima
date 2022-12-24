import TestsUtils.CodeGenAndRunTests

open Lurk.Backend.Value

open LSpec in
def main := do
  let tSeq ← extractCodeGenTests
    "Fixtures/CodeGeneration/TCFunctions.lean"
    [("runCheckStore", ⦃("Except" 1 NIL NIL ("PUnit" 0))⦄)]
  lspecIO tSeq
