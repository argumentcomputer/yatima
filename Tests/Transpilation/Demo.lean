import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Demo.lean"
    [
      extractIpldRoundtripTests,
      extractTranspilationTests [
        (`listLength, none),
        (`expr, none),
        (`univCtor, none)
        -- (`map', none)
      ]
    ]
  lspecIO tSeq
