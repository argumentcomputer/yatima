import LightData
import Std.Data.RBMap

def hexChar (u : UInt8) : Char :=
  match u with
  | 0  => '0' | 1  => '1' | 2  => '2' | 3  => '3' | 4  => '4' | 5 => '5'
  | 6  => '6' | 7  => '7' | 8  => '8' | 9  => '9' | 10 => 'a'
  | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e' | 15 => 'f' | _ => '*'

def ByteArray.asHex (bytes : ByteArray) : String :=
  let chars := bytes.data.foldr (init := []) fun b acc =>
    (hexChar $ b / 16) :: (hexChar $ b % 16) :: acc
  match chars with
  | '0' :: tail => ⟨tail⟩
  | x => ⟨x⟩

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

def persistData (data : LightData) (hash : Option $ ByteVector 32)
    (path : FilePath) : IO Unit := -- TODO : do it in a thread
  let bytes := Encodable.encode data
  let name := match hash with
    | some hash => hash.data.asHex
    | none => bytes.blake3.data.asHex
  IO.FS.writeBinFile (path / name) bytes

variable [h : Encodable (α × β) LightData String] [Ord α]

def loadRBMap (dir : FilePath) : IO $ Std.RBMap α β compare := do -- probably useless?
  let entries ← dir.readDir
  let mut ret : Array (α × β) := default
  for entry in entries do
    let path := entry.path
    let bytes ← IO.FS.readBinFile path
    match LightData.ofByteArray bytes with
    | .error e =>
      IO.println s!"Error when deserializing {path}: {e}"
      IO.FS.removeFile path
    | .ok ld => match h.decode ld with
      | .error e =>
        IO.println s!"Error when decoding {path}: {e}"
        IO.FS.removeFile path
      | .ok x => ret := ret.push x
  return .ofArray ret _
