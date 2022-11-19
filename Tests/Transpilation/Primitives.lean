import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Primitives.lean"
    [
      extractTranspilationTests [
        ("natAdd",  300)
      , ("natSub1", 98)
      -- , ("natSub2", 0)
      , ("natMul",  1024)
      , ("natDiv1", 0)
      , ("natDiv2", 33)
      -- , ("natMod1", 1)
      -- , ("natMod2", 37)
      , ("natLe",   ⟦(("Bool" 0 0) 1)⟧)
      , ("natBEqF", ⟦(("Bool" 0 0) 0)⟧)
      , ("natBEqT", ⟦(("Bool" 0 0) 1)⟧)
      -- , ("natEqF", ⟦(("Bool" 0 0) 0)⟧)
      -- , ("natEqT", ⟦(("Bool" 0 0) 1)⟧)
      -- , ("charA", 'a')
      -- , ("charOfNat", 'a')
      -- , ("charToNat", 97)
      , ("list", ⟦(1 2 3 4 5 6)⟧)
      -- , ("listMap", ⟦(2 3 4 5 6 7)⟧)
      -- , ("listFoldl", 21)
      , ("listBeq", ⟦(("Bool" 0 0) 1)⟧)
      -- , ("listEqF", ⟦(("Bool" 0 0) 0)⟧)
      , ("listEqT", ⟦(("Bool" 0 0) 1)⟧)
      , ("abcd", "abcd")
      , ("efg", "efg")
      , ("stringAppendInst", "abcdefg")
      , ("stringAppend", "abcdefg")
      -- , ("stringLength", 4)
      -- , ("stringAppendLength", 7)
      -- , ("stringBEqF", ⟦(("Bool" 0 0) 0)⟧)
      , ("stringBEqT", ⟦(("Bool" 0 0) 1)⟧)
      -- , ("stringEqF", ⟦(("Bool" 0 0) 0)⟧)
      , ("stringEqT", ⟦(("Bool" 0 0) 1)⟧)
      ]
    ]
  lspecIO tSeq
