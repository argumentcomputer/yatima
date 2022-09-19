import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/LurkTranslation/Demo.lean"
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
