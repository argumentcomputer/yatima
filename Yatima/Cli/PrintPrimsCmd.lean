import Yatima.Cli.Utils
import Yatima.ContAddr.ContAddr

open System Yatima.ContAddr

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

def printPrimsM (delta : List Lean.ConstantInfo) : ContAddrM Unit := do
  for const in delta do
    let name := const.name
    if primConstNames.contains name then
      let (c, _) ← getContAddrConst const
      IO.println s!"{c.anon.data} : {name}"

open Lean Elab in
def runFrontend (input : String) : IO Environment := do
  let inputCtx := Parser.mkInputContext input default
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header default messages inputCtx 0
  let env := env.setMainModule default
  let commandState := Command.mkState env messages default
  let s ← IO.processCommands inputCtx parserState commandState
  let msgs := s.commandState.messages
  if msgs.hasErrors then
    throw $ IO.userError $ "\n\n".intercalate $
      (← msgs.toList.mapM (·.toString)).map String.trim
  else return s.commandState.env

def printPrimsRun (_p : Cli.Parsed) : IO UInt32 := do
  Lean.setLibsPaths
  let env ← runFrontend primsInput
  let constants := env.constants
  let delta := constants.toList.filter (primConstNames.contains ·.1)
    |>.map Prod.snd
  discard $ ContAddrM.run (.init constants false) default (printPrimsM delta)
  return 0

def printPrimsCmd : Cli.Cmd := `[Cli|
  pp VIA printPrimsRun;
  "Prints the anon hashes for primitives"
]
