import TestsUtils.ContAddrAndExtractTests

def inductivesExtractor := extractAnonGroupsTests [
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
  lspecIO $ ← ensembleTestExtractors
    ("Fixtures" / "AnonGroups" / "Inductives.lean")
    [inductivesExtractor]
    [extractGeneralTests]
    false
