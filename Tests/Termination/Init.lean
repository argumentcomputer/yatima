import TestsUtils.ContAddrAndExtractTests

def initFixturesPath : System.FilePath :=
  "Fixtures" / "Termination" / "Init"

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors'
    [ initFixturesPath / "Prelude.lean",
      initFixturesPath / "Coe.lean",
      initFixturesPath / "Notation.lean",
      initFixturesPath / "Tactics.lean",
      initFixturesPath / "SizeOf.lean" ]
    []
    [extractGeneralTests]
