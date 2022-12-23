import TestsUtils.ContAddrAndExtractTests

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
  let tSeq ← contAddrAndExtractTests
    "Fixtures/AnonCidGroups/Inductives.lean"
    [inductivesExtractor, extractIpldTests, extractExtractorTests]
    false
  lspecIO tSeq
