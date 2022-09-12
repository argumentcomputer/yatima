import TestsUtils.TranspileTests

open LSpec in
def main := do
  let tSeq ← transpileTests
    "Fixtures/LurkInterpreter/NatTests.lean" 
    ⟦three⟧ (.ok 3)
  lspecIO tSeq