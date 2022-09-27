import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Demo.lean"
    [
      extractIpldTests,
      extractIpldRoundtripTests,
      extractTranspilationTests [
        (`listLength, none),
        (`expr, none),
        (`univCtor, none),
        (`mapInsert, none)
      ]
    ]
  lspecIO tSeq
