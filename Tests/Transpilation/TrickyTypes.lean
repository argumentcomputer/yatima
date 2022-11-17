import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/TrickyTypes.lean"
    [
      extractTranspilationTests [
        (`exprCtor, some "lam"),
        (`univCtor, some "zero"),
        (`treeSize, some 2),
        (`nameStr,  some "this.is.a.name")
      ]
    ]
  lspecIO tSeq
