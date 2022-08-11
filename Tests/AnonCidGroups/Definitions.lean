import TestsUtils.CompileAndExtractTests

def wellFoundedExtractor := extractAnonCidGroupsTests [
  [`WellFounded.A, `WellFounded.A'],
  [`WellFounded.B, `WellFounded.B'],
  [`WellFounded.C, `WellFounded.C'],
  [`WellFounded.E, `WellFounded.E'],
  [`WellFounded.F, `WellFounded.F'],
  [`WellFounded.G, `WellFounded.G'],
  [`WellFounded.H, `WellFounded.H'],
  [`WellFounded.I, `WellFounded.I']]

def partialExtractor := extractAnonCidGroupsTests [
  [`Partial.A, `Partial.C, `Partial.E, `Partial.F,
    `Partial.B, `Partial.G, `Partial.H],
  [`Partial.I]]

def unsafeExtractor := extractAnonCidGroupsTests [
  [`Unsafe.A, `Unsafe.C, `Unsafe.E, `Unsafe.F],
  [`Unsafe.B],
  [`Unsafe.G, `Unsafe.H], [`Unsafe.I]]

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/AnonCidGroups/Definitions.lean"
    [wellFoundedExtractor, partialExtractor, unsafeExtractor,
      extractIpldRoundtripTests]
  lspecIO tSeq
