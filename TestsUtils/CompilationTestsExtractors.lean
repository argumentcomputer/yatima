import LSpec
import Yatima.ContAddr.ContAddr
import Yatima.Commit.Commit

open LSpec Yatima ContAddr
open System (FilePath)

def withExceptOkIO (descr : String) (exc : Except ε α) [ToString ε]
    (f : α → IO TestSeq) : IO TestSeq :=
  match exc with
  | .error e => return test descr (ExpectationFailure "ok _" s!"error {e}")
  | .ok    a => return test descr true $ ← f a

def extractCompilationTests (source : FilePath)
  (extractors : List $ ContAddrState → IO TestSeq) (setPaths : Bool := true) :
    IO TestSeq := do
  if setPaths then Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile source) source
  let (constMap, delta) := leanEnv.getConstsAndDelta
  withExceptOkIO s!"Content-addresses {source}" (contAddr constMap delta)
    fun stt => extractors.foldlM (init := .done) fun acc ext =>
      do pure $ acc ++ (← ext stt)

def extractPersistenceTests (stt : ContAddrState) : IO TestSeq := do
  let storeAnon := stt.storeAnon
  let storeMeta := stt.storeMeta
  stt.dump "foo"
  sorry

section AnonCidGroups

open IR

/-
This section defines an extractor that consumes a list of groups of names and
creates tests that assert that:
1. Each pair of constants in the same group has the same anon hash
2. Each pair of constants in different groups has different anon hashes
-/

def extractCidGroups (groups : List (List Name)) (stt : ContAddrState) :
    Except String (Array (Array $ Name × Hash)) := Id.run do
  let mut notFound : Array Name := #[]
  let mut hashGroups : Array (Array $ Name × Hash) := #[]
  for group in groups do
    let mut hashGroup : Array (Name × Hash) := #[]
    for name in group do
      match stt.env.consts.find? name with
      | none        => notFound  := notFound.push name
      | some (h, _) => hashGroup := hashGroup.push (name, h)
    hashGroups := hashGroups.push hashGroup
  if notFound.isEmpty then
    return .ok hashGroups
  else
    return .error s!"Not found: {", ".intercalate $ notFound.data.map toString}"

def extractAnonCidGroupsTests (groups : List $ List Name)
    (stt : ContAddrState) : TestSeq :=
  withExceptOk "All constants can be found" (extractCidGroups groups stt)
    fun anonCidGroups =>
      let cidEqTests := anonCidGroups.foldl (init := .done) fun tSeq cidGroup =>
        cidGroup.data.pairwise.foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ = {y.1}ₐₙₒₙ" (x.2 == y.2)
      anonCidGroups.data.pairwise.foldl (init := cidEqTests) fun tSeq (g, g') =>
        (g.data.cartesian g'.data).foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ ≠ {y.1}ₐₙₒₙ" (x.2 != y.2)

end AnonCidGroups
