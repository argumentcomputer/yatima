import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr
import Yatima.Commit.Commit

open System Yatima.ContAddr Yatima.Commit

def primConstNames : Std.RBSet Lean.Name compare := .ofList [
  ``Nat, ``Bool, ``Bool.true, ``Bool.false, ``Nat.zero, ``String,
  ``Nat.add, ``Nat.mul, ``Nat.pow, ``Nat.beq, ``Nat.ble, ``Nat.blt, ``Nat.succ
] _

def primsInput : String :=
  let (defs, _) := primConstNames.foldl (init := ([], 0)) fun acc name =>
    let (l, i) := acc
    (s!"def x{i} := {name}" :: l, i + 1)
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

def formatMatchesP2F (pairs : List (Lean.Name × Lurk.F)) : List String :=
  pairs.map fun (n, f) => s!"  | {nameToPrimRepr n} => return .ofNat {f.val}"

def formatMatchesF2P (pairs : List (Lean.Name × Lurk.F)) : List String :=
  pairs.map fun (n, f) => s!"  | .ofNat {f.val} => return {nameToPrimRepr n}"

def targetFile : FilePath :=
  "Yatima" / "Typechecker" / "TypecheckM.lean"

def printPrimsRun (_p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend primsInput default
  let (constMap, delta) := leanEnv.getConstsAndDelta
  let caStt ← match contAddr constMap delta default with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  let anonHashes := caStt.env.consts.foldl (init := #[]) fun acc name (h, _) =>
    if primConstNames.contains name then acc.push h else acc

  let store := caStt.storeAnon

  let commits ← match ← commit anonHashes store false false with
  | .error e => IO.eprintln e; return 1 | .ok (_, comms) => pure comms.toList

  let commitsQuick ← match ← commit anonHashes store true false with
  | .error e => IO.eprintln e; return 1 | .ok (_, comms) => pure comms.toList

  let decls := primConstNames.toList

  let primFoF := "def primToF : PrimConst → Option F\n" ++
    "\n".intercalate (formatMatchesP2F $ decls.zip commits) ++ "\n"

  let fToPrim := "def fToPrim : F → Option PrimConst\n" ++
    "\n".intercalate (formatMatchesF2P $ decls.zip commits) ++ "\n  | _ => none\n"

  let primToFQuick := "def primToFQuick : PrimConst → Option F\n" ++
    "\n".intercalate (formatMatchesP2F $ decls.zip commitsQuick) ++ "\n"

  let fToPrimQuick := "def fToPrimQuick : F → Option PrimConst\n" ++
    "\n".intercalate (formatMatchesF2P $ decls.zip commitsQuick) ++ "\n  | _ => none\n"

  match (← IO.FS.readFile targetFile).splitOn "--PRIMBEGIN" with
  | [beg, en] => match en.splitOn "--PRIMEND" with
    | [_, en] =>
      let content :=
        beg ++ "--PRIMBEGIN\n" ++
        primFoF ++ fToPrim ++ primToFQuick ++ fToPrimQuick ++
        "--PRIMEND" ++ en
      IO.FS.writeFile targetFile content
      return 0
    | _ => IO.eprintln s!"Invalid format for {targetFile}"; return 1
  | _ => IO.eprintln s!"Invalid format for {targetFile}"; return 1

def printPrimsCmd : Cli.Cmd := `[Cli|
  pp VIA printPrimsRun;
  "Prints the commit hashes for primitives"
]
