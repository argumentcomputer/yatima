import LightData

def ByteArray.asHex : ByteArray → String := sorry

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

def mkDirs : IO Unit := do
  IO.FS.createDirAll STOREDIR
  SUBDIRS.forM IO.FS.createDir

def persistData (data : LightData) (path : FilePath) (genName := true) : IO Unit :=
  -- TODO : do it in a thread
  let bytes : ByteArray := Encodable.encode data
  let path := if genName then path / bytes.blake3.data.asHex else path
  IO.FS.writeBinFile path bytes
