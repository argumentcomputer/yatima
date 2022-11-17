import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Primitives.lean"
    [
      extractTranspilationTests [
        (`natAdd,  some 300)
      , (`natSub1, some 98)
      -- , (`natSub2, some 0)
      , (`natMul,  some 1024)
      , (`natDiv1, some 0)
      , (`natDiv2, some 33)
      -- , (`natMod1, some 1)
      -- , (`natMod2, some 37)
      , (`natLe, some ⟦((Bool 0 0) 1)⟧)
      , (`natBEqF, some ⟦((Bool 0 0) 0)⟧)
      , (`natBEqT, some ⟦((Bool 0 0) 1)⟧)
      -- , (`natEqF, some ⟦((Bool 0 0) 0)⟧)
      -- , (`natEqT, some ⟦((Bool 0 0) 1)⟧)
      -- , (`charA, some 'a')
      -- , (`charOfNat, some 'a')
      -- , (`charToNat, some 97)
      , (`list, some ⟦(1 2 3 4 5 6)⟧)
      -- , (`listMap, some ⟦(2 3 4 5 6 7)⟧)
      -- , (`listFoldl, some 21)
      , (`listBeq, some ⟦((Bool 0 0) 1)⟧)
      -- , (`listEqF, some ⟦((Bool 0 0) 0)⟧)
      , (`listEqT, some ⟦((Bool 0 0) 1)⟧)
      , (`abcd, some "abcd")
      , (`efg, some "efg")
      -- , (`stringAppend, some "abcdefg")
      -- , (`stringLength, some 4)
      -- , (`stringAppendLength, some 7)
      -- , (`stringBEqF, some ⟦((Bool 0 0) 0)⟧)
      , (`stringBEqT, some ⟦((Bool 0 0) 1)⟧)
      -- , (`stringEqF, some ⟦((Bool 0 0) 0)⟧)
      , (`stringEqT, some ⟦((Bool 0 0) 1)⟧)
      ]
    ]
  lspecIO tSeq
