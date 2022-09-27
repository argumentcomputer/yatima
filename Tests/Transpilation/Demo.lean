import TestsUtils.CompileAndExtractTests

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Demo.lean"
    [
      extractTranspilationTests [
        (`listLength, some 6),
        (`expr, none),
        (`univCtor, some "zero"),
        (`mapInsert, none),
        (`strAppend, some "abcdef"),
        (`treeSize, some 1),
        (`nameStr, some "this.is.a.name")
      ]
    ]
  lspecIO tSeq
