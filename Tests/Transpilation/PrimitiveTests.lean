import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/PrimitiveTests.lean"
    [
      extractTranspilationTests [
      -- it's easier to comment out tests with this comma placement lol
        (`natAdd, some $ .lit $ .num (.ofNat 300))
      -- , (`natSub1, some ⟦98⟧)
      -- , (`natSub2, some ⟦0⟧)
      -- , (`natMul, some ⟦1024⟧)
      -- , (`natDiv1, some ⟦0⟧)
      -- , (`natDiv2, some ⟦33⟧)
      -- , (`natMod1, some ⟦1⟧)
      -- , (`natMod2, some ⟦37⟧)
      -- , (`natLe, some ⟦$(``true)⟧)
      -- , (`natBeq, some ⟦$(``false)⟧)
      -- , (`natEq, some ⟦$(``false)⟧)
      -- , (`char, some ⟦'a'⟧)
      -- , (`charOfNat, some ⟦'a'⟧)
      -- , (`charToNat, some ⟦97⟧)
      -- , (`list, some ⟦,(1 2 3 4 5 6)⟧)
      -- , (`listMap, some ⟦,(2 3 4 5 6 7)⟧)
      -- , (`listFoldl, some ⟦21⟧)
      -- , (`listBeq, some ⟦$(``true)⟧)
      -- , (`listEq, some ⟦$(``false)⟧)
      -- , (`abcd, some ⟦"abcd"⟧)
      -- , (`egf, some ⟦"efg"⟧)
      -- , (`stringAppend, some ⟦"abcdefg"⟧)
      -- , (`stringLength, some ⟦7⟧)
      -- , (`stringBeq, some ⟦$(``false)⟧)
      -- , (`stringEq, some ⟦$(``false)⟧)
      ]
    ]
  lspecIO tSeq
