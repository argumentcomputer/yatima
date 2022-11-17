import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/TrickyTypes.lean"
    [
      extractTranspilationTests [
        -- (`exprCtor, some $ .lit $ .str "lam"),
        -- (`univCtor, some $ .lit $ .str "zero"),
        -- (`treeSize, some $ .lit $ .num (.ofNat 2)),
        -- (`nameStr,  some $ .lit $ .str "this.is.a.name")
      ]
    ]
  lspecIO tSeq
