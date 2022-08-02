import TestsUtils.CompileAndExtractTests

def wellFoundedExtractor := extractAnonCidGroupsTests [
  [`A, `A'],
  [`B, `B'],
  [`C, `C'],
  [`E, `E'],
  [`F, `F'],
  [`G, `G'],
  [`H, `H'],
  [`I, `I']]

def partialExtractor := extractAnonCidGroupsTests
  [[`A, `C, `E, `F, `B, `G, `H], [`I]]

def unsafeExtractor := extractAnonCidGroupsTests
  [[`A, `C, `E, `F], [`B], [`G, `H], [`I]]

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/AnonCidGroups/Definitions.lean"
    [wellFoundedExtractor, partialExtractor, unsafeExtractor]
  lspecIO tSeq
