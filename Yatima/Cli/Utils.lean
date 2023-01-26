import Yatima.Datatypes.Env
import LightData

open Yatima.IR (Env)

variable [h : Encodable Yatima.IR.Env LightData String]

def loadEnv (envFileName : String) : IO $ Except String Env := do
  match LightData.ofByteArray (← IO.FS.readBinFile ⟨envFileName⟩) with
  | .error e => return .error s!"Error deserializing input environment: {e}"
  | .ok data => match h.decode data with
    | .error e => return .error s!"Error decoding input environment: {e}"
    | .ok env => return .ok env
