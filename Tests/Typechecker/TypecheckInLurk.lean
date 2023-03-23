import TestsUtils.ContAddrAndExtractTests

open LSpec in
def main := do
  lspecIO $ ← ensembleTestExtractors
    ("Fixtures" / "Typechecker" / "TypecheckInLurk.lean")
    []
    [extractLurkTypecheckTests [`id', `PUnit', `Unit', `Nat', `natAdd, `add_comm]]
    true
    false
