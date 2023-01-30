import Cli.Basic
import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr
import Yatima.Commit.Commit

open System Yatima.ContAddr Yatima.Commit

def primConstNames : Std.RBSet Lean.Name compare := .ofList [
  ``Nat, ``Bool, ``Bool.true, ``Bool.false, ``Nat.zero, ``String,
  ``Nat.add, ``Nat.mul, ``Nat.pow, ``Nat.beq, ``Nat.ble, ``Nat.blt, ``Nat.succ
] _

def primsInput := "
def nat := Nat
def bool_ := Bool
def boolFalse := Bool.false
def boolTrue := Bool.true
def natZero := Nat.zero
def string := String
def natAdd := Nat.add
def natMul := Nat.mul
def natPow := Nat.pow
def natBeq := Nat.beq
def natBle := Nat.ble
def natBlt := Nat.blt
def natSucc := Nat.succ
"

def printPrimsRun (_p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let leanEnv ← Lean.runFrontend primsInput default
  let (constMap, delta) := leanEnv.getConstsAndDelta
  let delta := delta.filter (primConstNames.contains ·.name)
  let caStt ← match contAddr constMap delta default with
    | .error err => IO.eprintln err; return 1
    | .ok stt => pure stt
  let anonHashes := caStt.env.consts.foldl (init := #[]) fun acc name (h, _) =>
    if primConstNames.contains name then acc.push h else acc
  
  let store := caStt.storeAnon

  let (_, commits) ← match ← commit anonHashes store false false with
  | .error e => IO.eprintln e; return 1
  | .ok comms => pure comms

  let (_, commitsQuick) ← match ← commit anonHashes store true false with
  | .error e => IO.eprintln e; return 1
  | .ok comms => pure comms

  let decls := primConstNames.toList

  IO.println "Primitive hashes"
  decls.zip commits.toList |>.forM IO.println

  IO.println "\nPrimitive hashes (quick)"
  decls.zip commitsQuick.toList |>.forM IO.println

  return 0

def printPrimsCmd : Cli.Cmd := `[Cli|
  pp VIA printPrimsRun;
  "Prints the commit hashes for primitives"
]
