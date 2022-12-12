import Lean
import Std.Data.RBMap
import YatimaStdLib.Lean

namespace Lean

def ConstantInfo.formatAll (c : ConstantInfo) : String :=
  match c.all with
  | [ ]
  | [_] => ""
  | all => " " ++ all.toString

def ConstantInfo.ctorName : ConstantInfo → String
  | axiomInfo  _ => "axiom"
  | defnInfo   _ => "definition"
  | thmInfo    _ => "theorem"
  | opaqueInfo _ => "opaque"
  | quotInfo   _ => "quotient"
  | inductInfo _ => "inductive"
  | ctorInfo   _ => "constructor"
  | recInfo    _ => "recursor"

def ConstMap.childrenOfWith (map : ConstMap) (name : Name)
    (p : ConstantInfo → Bool) : List ConstantInfo :=
  map.fold (init := []) fun acc n c => match n with
  | .str n ..
  | .num n .. => if n == name && p c then c :: acc else acc
  | _ => acc

open Elab in
def runFrontend (input : String) (fileName : String := default) :
    IO $ Option String × Environment := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header default messages inputCtx 0
  let env := env.setMainModule default
  let commandState := Command.mkState env messages default

  let s ← IO.processCommands inputCtx parserState commandState
  let msgs := s.commandState.messages
  let errMsg := if msgs.hasErrors
    then some $ "\n\n".intercalate $
      (← msgs.toList.mapM (·.toString)).map String.trim
    else none
  return (errMsg, s.commandState.env)

/--
Sets the directories where `olean` files can be found.

This function must be called before `compile` if the file to be compiled has
imports (the automatic imports from `Init` also count).
-/
def setLibsPaths : IO Unit := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["print-paths"]
  }
  let split := out.stdout.splitOn "\"oleanPath\":[" |>.getD 1 ""
  let split := split.splitOn "],\"loadDynlibPaths\":[" |>.getD 0 ""
  let paths := split.replace "\"" "" |>.splitOn ","|>.map System.FilePath.mk
  Lean.initSearchPath (← Lean.findSysroot) paths

end Lean

instance : HMul Ordering Ordering Ordering where hMul
  | .gt, _ => .gt
  | .lt, _ => .lt
  | .eq, x => x

def concatOrds : List Ordering → Ordering :=
  List.foldl (fun x y => x * y) .eq

def Lean.PersistentHashMap.filter [BEq α] [Hashable α]
    (map : PersistentHashMap α β) (p : α → β → Bool) : PersistentHashMap α β :=
  map.foldl (init := .empty) fun acc x y =>
    match p x y with
    | true => acc.insert x y
    | false => acc

section

variable [BEq α] [Hashable α] [Monad m]

def Lean.HashMap.map (hmap : Lean.HashMap α β) (f : β → σ) : Lean.HashMap α σ :=
  hmap.fold (init := default) fun acc a b => acc.insert a (f b)

def Lean.SMap.map (smap : Lean.SMap α β) (f : β → σ) : Lean.SMap α σ :=
  let m₁ := smap.map₁.map f
  let m₂ := smap.map₂.map f
  ⟨smap.stage₁, m₁, m₂⟩

end 

open Lean in
def patchUnsafeRec (cs : ConstMap) : ConstMap :=
  let unsafes : Std.RBSet Name compare :=
    cs.fold (init := .empty) fun acc n _ => match n with
    | .str n "_unsafe_rec" => acc.insert n
    | _ => acc
  cs.map fun c => match c with
    | .opaqueInfo o =>
      if unsafes.contains o.name then
        .opaqueInfo ⟨
          o.toConstantVal, mkConst (o.name ++ `_unsafe_rec),
          o.isUnsafe, o.levelParams
        ⟩
      else
        .opaqueInfo o
    | c => c