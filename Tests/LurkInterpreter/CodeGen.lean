import TestsUtils.TranspileTests

open LSpec in
def main := do
  let tSeq ← transpileTests
    "Fixtures/LurkInterpreter/NatTests.lean" 
    ⟦whee⟧ (.ok 6)
  lspecIO tSeq