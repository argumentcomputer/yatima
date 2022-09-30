import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Demo.lean"
    [
      extractIpldTests,
      extractIpldRoundtripTests,
      extractTranspilationTests [
        (`expr, none),
        (`univCtor, some ⟦"zero"⟧),
        (`mapInsert, none),
        (`treeSize, some ⟦1⟧)
      ]
    ]
  lspecIO tSeq
