import Yatima.Graph.Tree

namespace Lean

namespace List

def eraseDup [BEq α] : List α → List α
  | [] => []
  | x::xs => 
    let exs := eraseDup xs
    if exs.contains x then exs else x::exs

end List

open Std (RBMap)

instance : Ord Name :=
 { compare := fun x y => compare (toString x) (toString y) }

abbrev ReferenceMap := RBMap Name (List Name) Ord.compare

def ReferenceMap.empty := @RBMap.empty Name (List Name) Ord.compare

instance : Inhabited ReferenceMap := 
  { default := ReferenceMap.empty }

mutual 

  partial def getExprRefs (expr : Expr) : List Name :=
    match expr with 
    | .const name _ _ => [name]
    | .app func arg _ => 
      getExprRefs func ++  getExprRefs arg
    | .lam name type body _ => 
      getExprRefs type ++  getExprRefs body
    | .forallE name type body _ => 
      getExprRefs type ++  getExprRefs body
    | .letE  name type body exp _ => 
      getExprRefs type ++  getExprRefs body ++ getExprRefs exp
    | .proj name idx exp _ => getExprRefs exp
    | _ => []

  partial def getConstRefs (const : ConstantInfo) : List Name :=
    match const with 
    | .axiomInfo  val => getExprRefs val.type
    | .defnInfo   val => 
      getExprRefs val.type ++ getExprRefs val.value
    | .thmInfo    val => 
      getExprRefs val.type ++ getExprRefs val.value
    | .opaqueInfo val => 
      getExprRefs val.type ++ getExprRefs val.value
    | .ctorInfo   val => 
      val.induct :: getExprRefs val.type
    | .inductInfo val => 
      getExprRefs val.type ++ val.ctors ++ val.all
    | .recInfo    val => 
      getExprRefs val.type ++ val.all ++ val.rules.map RecursorRule.ctor
    | .quotInfo   val => getExprRefs val.type

end

def referenceMap (constMap : ConstMap) : ReferenceMap :=
  SMap.fold 
    (fun acc name const => acc.insert name $ List.eraseDup $ getConstRefs const) 
    ReferenceMap.empty 
    constMap

instance : ToString ReferenceMap := 
 { toString := fun refs => toString refs.toList }

-- def detectCycles (constMap : ConstMap) : List (List Name) := sorry

end Lean

abbrev Graph := Lean.ReferenceMap
abbrev Vertex := Lean.Name
abbrev Edge := Lean.Name × Lean.Name

open Lean Std
namespace Graph

def vertices (g : Graph) : List Vertex :=
  g.toList.map Prod.fst

def edges (g : Graph) : List Edge := 
  (g.toList.map fun (x, xs) => xs.map fun y => ⟨x, y⟩).join

def buildG (edges : List Edge) : Graph :=
  List.foldl (fun g e => 
    match g.find? e.1 with 
    | some v => g.insert e.1 $ e.2 :: v
    | none => g.insert e.1 [e.2]
  ) Lean.ReferenceMap.empty edges

def reverseE (g : Graph) : List Edge :=
  g.edges.map fun (v, w) => (w, v)

def transposeG (g : Graph) : Graph :=
  buildG g.reverseE

open Std in 
def outDegrees (g : Graph) : RBMap Name Nat compare :=
  RBMap.fromList (g.toList.map fun (x, xs) => (x, xs.length)) compare

def outDegree (g : Graph) (v : Vertex) : Option Nat :=
  List.length <$> g.find? v

open Std in 
def inDegrees (g : Graph) : RBMap Name Nat compare :=
  g.fold (fun degrees x xs => 
    xs.foldl (fun acc v => 
      match acc.find? v with 
      | some n => acc.insert v (n + 1)
      | none => acc.insert v 1
    ) degrees
  ) RBMap.empty

open Std in 
/-- Not sure which one is better? -/
def inDegrees' (g : Graph) : RBMap Name Nat compare :=
  g.transposeG.outDegrees

/-- Don't use this, it will recompute `g.inDegrees` every time, yuck! -/
def inDegree (g : Graph) (v : Vertex) : Option Nat :=
  g.inDegrees.find? v

structure dfsState where 
 visited : RBMap Name Bool compare

abbrev dfsM := ReaderT Graph $ EStateM String dfsState

partial def generate (v : Vertex) : dfsM $ Tree Vertex := do
  match (← get).visited.find? v with
  | some _ => pure .empty
  | none => do
    set { ← get with visited := (← get).visited.insert v true }
    match (← read).find? v with 
    | some vs => do
      let ts ← vs.mapM generate
      pure $ .node v $ ts.filter Tree.isEmpty
    | none => throw s!"Vertex {v} not in graph"

def generateVs (vs : List Vertex) : dfsM $ List $ Tree Vertex := do 
  vs.mapM generate

def dfsM.run (g : Graph) (v : Vertex) : Except String $ Tree Vertex  :=
  match EStateM.run (ReaderT.run (generate v) g) { visited := .empty } with 
  | .ok res state => .ok res 
  | .error e _ => .error e

def dfs (g : Graph) (vs : List Vertex) : Except String $ List $ Tree Vertex :=
  match EStateM.run (ReaderT.run (generateVs vs) g) { visited := .empty } with 
  | .ok res state => .ok res 
  | .error e _ => .error e

def dff (g : Graph) : Except String $ List $ Tree Vertex :=
  g.dfs g.vertices 

end Graph
