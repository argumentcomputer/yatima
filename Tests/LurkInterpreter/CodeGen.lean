import TestsUtils.TranspileTests

open LSpec in
def main := do
  let tSeq ← transpileTests
    [
      "Fixtures/LurkTranslation/DemoExpr.lean",
      "Fixtures/LurkTranslation/DemoList.lean",
      "Fixtures/LurkTranslation/DemoUniv.lean"
    ]
    ⟦root⟧ (.ok 0)
  lspecIO tSeq