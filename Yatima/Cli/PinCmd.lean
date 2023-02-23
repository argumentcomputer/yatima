import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr

open System Yatima.ContAddr

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

def pinRun (_p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend primsInput default
  let (constMap, delta) := leanEnv.getConstsAndDelta

  let commits ← match ← contAddr constMap delta default true false with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure $ stt.env.consts.toList.filter fun (n, _) =>
      primConstNames.contains n

  let commitsQuick ← match ← contAddr constMap delta default true false with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure $ stt.env.consts.toList.filter fun (n, _) =>
      primConstNames.contains n

  let primFoF := "def primToF : PrimConst → Option F\n" ++
    "\n".intercalate (formatMatchesP2F commits) ++ "\n"

  let fToPrim := "def fToPrim : F → Option PrimConst\n" ++
    "\n".intercalate (formatMatchesF2P commits) ++ "\n  | _ => none\n"

  let primToFQuick := "def primToFQuick : PrimConst → Option F\n" ++
    "\n".intercalate (formatMatchesP2F commitsQuick) ++ "\n"

  let fToPrimQuick := "def fToPrimQuick : F → Option PrimConst\n" ++
    "\n".intercalate (formatMatchesF2P commitsQuick) ++ "\n  | _ => none\n"

  match (← IO.FS.readFile targetFile).splitOn "--PIN" with
  | [beg, _, en] =>
    IO.FS.writeFile targetFile $
      beg ++ "--PIN\n" ++
      primFoF ++ fToPrim ++ primToFQuick ++ fToPrimQuick ++
      "--PIN" ++ en
    return 0
  | _ => IO.eprintln s!"Invalid format for {targetFile}"; return 1

def pinCmd : Cli.Cmd := `[Cli|
  pin VIA pinRun;
  "Edits the source file TypecheckM.lean file with the commit hashes for primitives"
]
