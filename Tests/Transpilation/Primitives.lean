import TestsUtils.CompileAndExtractTests

open Lurk.Syntax.DSL

def toNum (n : Nat) : Option Lurk.Evaluation.Value :=
  some $ .lit $ .num (.ofNat n)

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/Transpilation/Primitives.lean"
    [
      extractTranspilationTests [
        (`natAdd,  toNum 300)
      , (`natSub1, toNum 98)
      -- , (`natSub2, toNum 0)
      , (`natMul,  toNum 1024)
      , (`natDiv1, toNum 0)
      , (`natDiv2, toNum 33)
      -- , (`natMod1, toNum 1)
      -- , (`natMod2, toNum 37)
      -- , (`natLe, some $ .sym $ "Bool.true")
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
