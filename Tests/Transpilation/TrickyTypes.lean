import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/TrickyTypes.lean"
    [
      extractTranspilationTests [
        -- ("exprCtor", "lam"),
        -- ("univCtor", "zero"),
        -- ("treeSize", 2),
        -- ("nameStr",  "this.is.a.name")
      ]
    ]
  lspecIO tSeq
