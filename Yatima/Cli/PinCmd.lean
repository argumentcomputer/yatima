import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr

open System Yatima.ContAddr

def primConstNames : Std.RBSet Lean.Name compare := .ofList [
  ``Nat, ``Bool, ``Bool.true, ``Bool.false, ``Nat.zero, ``String,
  ``Nat.add, ``Nat.mul, ``Nat.pow, ``Nat.beq, ``Nat.ble, ``Nat.blt, ``Nat.succ
] _

def allowedAxiomNames : Std.RBSet Lean.Name compare := .ofList [
  ``Classical.choice, ``propext, ``Quot.sound, ``Lean.ofReduceBool,
  ``Lean.ofReduceNat
] _

def primsInput : String :=
  let (defs, _) := primConstNames.union allowedAxiomNames |>.foldl (init := ([], 0))
    fun acc name => let (l, i) := acc; (s!"noncomputable def x{i} := @{name}" :: l, i + 1)
  "\n".intercalate defs

def nameToPrimRepr : Lean.Name → String
  | ``Nat        => ".nat"
  | ``Nat.zero   => ".natZero"
  | ``Bool       => ".bool"
  | ``Bool.true  => ".boolTrue"
  | ``Bool.false => ".boolFalse"
  | ``String     => ".string"
  | ``Nat.add    => ".op .natAdd"
  | ``Nat.mul    => ".op .natMul"
  | ``Nat.pow    => ".op .natPow"
  | ``Nat.beq    => ".op .natBeq"
  | ``Nat.blt    => ".op .natBlt"
  | ``Nat.ble    => ".op .natBle"
  | ``Nat.succ   => ".op .natSucc"
  | x => panic! s!"Invalid name: {x}"

private def printDigest (f : Lurk.Digest) : String :=
  s!"#[.ofNat {f[0]!}, .ofNat {f[1]!}, .ofNat {f[2]!}, .ofNat {f[3]!}, .ofNat {f[4]!}, .ofNat {f[5]!}, .ofNat {f[6]!}, .ofNat {f[7]!}]"

def formatMatchesP2F (pairs : List (Lean.Name × Lurk.Digest)) : List String :=
  pairs.map fun (n, f) =>
    s!"  | {nameToPrimRepr n} => .some {printDigest f}"

def formatMatchesF2P (pairs : List (Lean.Name × Lurk.Digest)) : String := Id.run do
  let len := pairs.length
  let (firstName, firstDigest) := pairs.head!
  let mut ifThenBlock : String := s!"if digest == {printDigest firstDigest} then .some ({nameToPrimRepr firstName}) else\n"

  for (name, digest) in (pairs.take (len - 1)).drop 1 do
    ifThenBlock := ifThenBlock ++ s!"if digest == {printDigest digest} then .some ({nameToPrimRepr name}) else\n"

  return ifThenBlock ++ s!".none\n"

def formatMatchesF2B (fs : List Lurk.Digest) : String := Id.run do
  let len := fs.length
  let firstDigest := fs.head!
  let mut ifThenBlock : String := s!"if digest == {printDigest firstDigest} then true else\n"

  for digest in (fs.take (len - 1)).drop 1 do
    ifThenBlock := ifThenBlock ++ s!"if digest == {printDigest digest} then true else\n"

  return ifThenBlock ++ s!"false\n"

def targetFile : FilePath :=
  "Yatima" / "Typechecker" / "TypecheckM.lean"

def pinRun (_p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend primsInput default
  let (constMap, delta) := leanEnv.getConstsAndDelta

  let commits ← match ← contAddr constMap delta false false with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure $ stt.env.consts.toList

  let commitsQuick ← match ← contAddr constMap delta true false with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure $ stt.env.consts.toList

  let primCommits := commits.filter fun (n, _) => primConstNames.contains n
  let primCommitsQuick := commitsQuick.filter fun (n, _) => primConstNames.contains n

  let primFoF := "def primToF : PrimConst → Option Digest\n" ++
    "\n".intercalate (formatMatchesP2F primCommits) ++ "\n\n"

  let fToPrim := "def fToPrim (digest : Digest) : Option PrimConst :=\n" ++
    formatMatchesF2P primCommits ++ "\n\n"

  let primToFQuick := "def primToFQuick : PrimConst → Option Digest\n" ++
    "\n".intercalate (formatMatchesP2F primCommitsQuick) ++ "\n\n"

  let fToPrimQuick := "def fToPrimQuick (digest : Digest) : Option PrimConst :=\n" ++
    formatMatchesF2P primCommitsQuick ++ "\n\n"

  let axiomsCommits :=
    (commits.filter fun (n, _) => allowedAxiomNames.contains n).map (·.2)

  let axiomsCommitsQuick :=
    (commitsQuick.filter fun (n, _) => allowedAxiomNames.contains n).map (·.2)

  let allowedAxiom := "def allowedAxiom (digest : Digest) : Bool :=\n" ++
    formatMatchesF2B axiomsCommits ++ "\n\n"

  let allowedAxiomQuick := "def allowedAxiomQuick (digest : Digest) : Bool :=\n" ++
    formatMatchesF2B axiomsCommitsQuick ++ "\n\n"

  match (← IO.FS.readFile targetFile).splitOn "--PIN" with
  | [beg, _, en] =>
    IO.FS.writeFile targetFile $
      beg ++ "--PIN\n" ++
      primFoF ++ fToPrim ++ primToFQuick ++ fToPrimQuick ++
      allowedAxiom ++ allowedAxiomQuick ++
      "--PIN" ++ en
    return 0
  | _ => IO.eprintln s!"Invalid format for {targetFile}"; return 1

def pinCmd : Cli.Cmd := `[Cli|
  pin VIA pinRun;
  "Edits the file TypecheckM.lean with pinned hashes for primitives and allowed axioms"
]
