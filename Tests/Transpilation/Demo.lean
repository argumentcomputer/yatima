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
        (`univCtor, some ⟦"zero"⟧),
        (`mapInsert, none),
        (`treeSize, some ⟦1⟧)
      ]
    ]
  lspecIO tSeq
