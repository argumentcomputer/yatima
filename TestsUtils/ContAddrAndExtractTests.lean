import LSpec
import Yatima.ContAddr.ContAddr
import Yatima.Commit.Commit
import Yatima.Typechecker.Typechecker

open LSpec Yatima IR ContAddr Commit Typechecker
open System (FilePath)

-- Move to LSpec
@[specialize]
def withExceptOkM [Monad m] (descr : String) (exc : Except ε α) [ToString ε]
    (f : α → m TestSeq) : m TestSeq :=
  match exc with
  | .error e => return test descr (ExpectationFailure "ok _" s!"error {e}")
  | .ok    a => return test descr true $ ← f a

abbrev Extractor := ContAddrState → TestSeq
abbrev IOExtractor := ContAddrState → IO TestSeq

/-- Run tests from extractors given a Lean source file -/
def ensembleTestExtractors (source : FilePath)
  (extractors : List Extractor) (ioExtractors : List IOExtractor)
    (setPaths : Bool := true) : IO TestSeq := do
  if setPaths then Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend (← IO.FS.readFile source) source
  let (constMap, delta) := leanEnv.getConstsAndDelta
  withExceptOkM s!"Content-addresses {source}" (contAddr constMap delta)
    fun stt => do
      let pureTests := extractors.foldl (init := .done)
        fun acc ext => acc ++ (ext stt)
      ioExtractors.foldlM (init := pureTests) fun acc ext =>
        do pure $ acc ++ (← ext stt)

/-- Calls `ensembleTestExtractors` for multiple sources -/
def ensembleTestExtractors' (sources : List FilePath)
  (extractors : List Extractor) (ioExtractors : List IOExtractor)
    (setPaths : Bool := true) : IO TestSeq :=
  sources.foldlM (init := .done) fun acc source => do
    let g := group s!"Tests for {source}"
      (← ensembleTestExtractors source extractors ioExtractors setPaths)
    pure $ acc ++ g

/--
This extractor creates general tests that we expect from any Lean source:
1. Anon and meta stores can be loaded from FS after being persisted
2. Loaded stores match the persisted stores
3. The anon hashes can be committed successfully
4. After committed, the commits and consts maps have the same keys
5. Everything should typecheck successfully
-/
def extractGeneralTests : IOExtractor := fun stt => do
  let storeAnon := stt.storeAnon
  let (names, anonHashes) := 
    stt.env.consts.foldl (init := (#[], #[])) 
      fun (names, anonHashes) n (h, _) => (names.push n, anonHashes.push h)
  stt.dump "env.yenv"
  let storeRoundtripTests ← withExceptOkM "Loads the anon store"
      (← StoreAnon.load anonHashes) fun storeAnon' => do
    pure $ withExceptOk "Loads the meta store"
        (← StoreMeta.load stt.env.metaHashes) fun storeMeta' =>
      test "Anon store roundtrips" (storeAnon == storeAnon') ++
      test "Meta store roundtrips" (stt.storeMeta == storeMeta')
  let commitAndTypecheckTests ← withExceptOkM "Committing succeeds"
      (← commit anonHashes storeAnon true false)
    fun (cmStt, comms) => pure $
      let fmap : Std.RBMap Lurk.F Lean.Name compare :=
        (names.zip comms).foldl (init := .empty) fun acc (name, comm) =>
          acc.insert comm name
      test "Consts and commits have the same keys"
        (cmStt.consts.keysArray == cmStt.commits.keysArray) ++
      withExceptOk "Typechecking succeeds" (typecheckAll cmStt.tcStore fmap)
        fun _ => .done
  return storeRoundtripTests ++ commitAndTypecheckTests

section AnonHashGroups

/-
This section defines an extractor that consumes a list of groups of names and
creates tests that assert that:
1. Each pair of constants in the same group has the same anon hash
2. Each pair of constants in different groups has different anon hashes
-/

def extractAnonGroups (groups : List (List Name)) (stt : ContAddrState) :
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

def extractAnonGroupsTests (groups : List $ List Name) : Extractor := fun stt =>
  withExceptOk "All constants can be found" (extractAnonGroups groups stt)
    fun anonGroups =>
      let anonEqTests := anonGroups.foldl (init := .done) fun tSeq anonGroup =>
        anonGroup.data.pairwise.foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ = {y.1}ₐₙₒₙ" (x.2 == y.2)
      anonGroups.data.pairwise.foldl (init := anonEqTests) fun tSeq (g, g') =>
        (g.data.cartesian g'.data).foldl (init := tSeq) fun tSeq (x, y) =>
          tSeq ++ test s!"{x.1}ₐₙₒₙ ≠ {y.1}ₐₙₒₙ" (x.2 != y.2)

end AnonHashGroups
