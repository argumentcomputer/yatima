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
  match ← IO.getEnv "XDG_CACHE_HOME" with
  | some path => return path / "yatima_store"
  | none => match ← IO.getEnv "HOME" with
    | some path => return path / ".cache" / "yatima_store"
    | none => throw $ .userError "Environment variable HOME is not defined"

def UNIVANONDIR : FilePath :=
  STOREDIR / "univ_anon"

def UNIVMETADIR : FilePath :=
  STOREDIR / "univ_meta"

def EXPRANONDIR : FilePath :=
  STOREDIR / "expr_anon"

def EXPRMETADIR : FilePath :=
  STOREDIR / "expr_meta"

def CONSTANONDIR : FilePath :=
  STOREDIR / "const_anon"

def CONSTMETADIR : FilePath :=
  STOREDIR / "const_meta"

def UNIVDIR : FilePath :=
  STOREDIR / "univ"

def EXPRDIR : FilePath :=
  STOREDIR / "expr"

def CONSTDIR : FilePath :=
  STOREDIR / "const"

def COMMITSDIR : FilePath :=
  STOREDIR / "commits"

def LDONHASHCACHE : FilePath :=
  STOREDIR / "ldon_hash_cache"

def SUBDIRS : List FilePath := [
  UNIVANONDIR, UNIVMETADIR,
  EXPRANONDIR, EXPRMETADIR,
  CONSTANONDIR, CONSTMETADIR,
  UNIVDIR, EXPRDIR, CONSTDIR
]

@[inline] def mkDirs : IO Unit :=
  SUBDIRS.forM IO.FS.createDirAll

def dumpData (data : LightData) (path : FilePath) : IO Unit :=
  -- TODO : do it in a thread
  let bytes := Encodable.encode data
  IO.FS.writeBinFile path bytes

variable [h : Encodable α LightData String]

def loadData (path : FilePath) : IO $ Option α := do
  if !(← path.pathExists) then return none
  match LightData.ofByteArray (← IO.FS.readBinFile path) with
  | .error e =>
    IO.println s!"Error when deserializing {path}: {e}"
    IO.FS.removeFile path
    return none
  | .ok data => match h.decode data with
    | .error e =>
      IO.println s!"Error when decoding {path}: {e}"
      IO.FS.removeFile path
      return none
    | .ok a => return some a
