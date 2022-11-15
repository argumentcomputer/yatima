import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Demo.lean"
    [
      extractIpldTests,
      extractConverterTests,
      extractTranspilationTests [
        (`expr, none),
        (`univCtor, some $ .sym "zero"),
        (`mapInsert, none),
        (`treeSize, some $ .lit $ .num (.ofNat 1))
      ]
    ]
  lspecIO tSeq
