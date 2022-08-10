import TestsUtils.CompileAndExtractTests

def inductivesExtractor := extractAnonCidGroupsTests [
  [`BLA, `BLU],
  [`BLA'],
  [`BLE, `BLE'],
  [`BLI, `BLI'],
  [`BLO, `BLO'],
  [`BLE''],
  [`BLI''],
  [`BLO''],
  [`BLEH]]

open LSpec in
def main := do
  let tSeq ← compileAndExtractTests
    "Fixtures/AnonCidGroups/Inductives.lean"
    [inductivesExtractor, extractIpldRoundtripTests]
    false
  lspecIO tSeq
