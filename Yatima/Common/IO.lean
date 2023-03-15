import LightData
import Std.Data.RBMap

def ByteArray.toHex (bytes : ByteArray) : String :=
  let to : UInt8 → Char
    | 0  => '0' | 1  => '1' | 2  => '2' | 3  => '3'
    | 4  => '4' | 5  => '5' | 6  => '6' | 7  => '7'
    | 8  => '8' | 9  => '9' | 10 => 'a' | 11 => 'b'
    | 12 => 'c' | 13 => 'd' | 14 => 'e' | 15 => 'f'
    | _ => unreachable!
  let chars := bytes.data.foldr (init := []) fun b acc =>
    (to $ b / 16) :: (to $ b % 16) :: acc
  match chars with
  | '0' :: tail => ⟨tail⟩
  | x => ⟨x⟩

def ByteArray.ofHex (hex : String) : Option ByteArray :=
  let hex := if hex.length % 2 == 1 then "0" ++ hex else hex
  let to : Char → Option UInt8
    | '0' => some 0  | '1' => some 1  | '2' => some 2  | '3' => some 3
    | '4' => some 4  | '5' => some 5  | '6' => some 6  | '7' => some 7
    | '8' => some 8  | '9' => some 9  | 'a' => some 10 | 'b' => some 11
    | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
    | _ => none
  let rec aux (acc : Array UInt8) : List Char → Option (Array UInt8)
    | x :: y :: tail => do aux (acc.push $ 16 * (← to x) + (← to y)) tail
    | _ => acc
  return ⟨← aux #[] hex.data⟩

open System (FilePath)

initialize STOREDIR : FilePath ← do
  match ← IO.getEnv "HOME" with
  | some path => return path / ".yatima"
  | none => throw $ IO.userError "can't find home folder"

def TCHASH : FilePath :=
  STOREDIR / "tc_hash"

def LDONHASHCACHE : FilePath :=
  STOREDIR / "ldon_hash_cache"

variable [h : Encodable α LightData]

def dumpData (data : α) (path : FilePath) (overwite := true) : IO Unit := do
  -- TODO : do it in a thread
  if overwite || !(← path.pathExists) then
    let ldata := h.encode data
    IO.FS.writeBinFile path ldata.toByteArray

def loadData (path : FilePath) (deleteIfCorrupted := true) : IO $ Option α := do
  if !(← path.pathExists) then return none
  match LightData.ofByteArray (← IO.FS.readBinFile path) with
  | .error e =>
    IO.println s!"Error when deserializing {path}: {e}"
    if deleteIfCorrupted then IO.FS.removeFile path
    return none
  | .ok data => match h.decode data with
    | .error e =>
      IO.println s!"Error when decoding {path}: {e}"
      if deleteIfCorrupted then IO.FS.removeFile path
      return none
    | .ok a => return some a
