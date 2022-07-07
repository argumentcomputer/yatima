import Yatima.Compiler.Utils
import Yatima.ForStdLib
import YatimaStdLib.RBNode
import YatimaStdLib.List
/-
This graph API needs work beforing being factored out because it's specific to
Lean types.

Another point: we'll soon drop the need for this API once we migrate to an
updated toolchain.
-/

namespace Lean

open Std (RBMap)

abbrev ReferenceMap := RBMap Name (List Name) compare

def ReferenceMap.empty : ReferenceMap :=
  .empty

instance : Inhabited ReferenceMap := 
  { default := .empty } 

def referenceMap (constMap : ConstMap) : ReferenceMap :=
  constMap.fold (init := .empty)
    fun acc name const => acc.insert name $ (getConstRefs const).eraseDupB

instance : ToString ReferenceMap := 
 { toString := fun refs => toString refs.toList }

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

-- /-- Don't use this, it will recompute `g.inDegrees` every time, yuck! -/
-- def inDegree (g : Graph) (v : Vertex) : Option Nat :=
--   g.inDegrees.find? v

structure dfsState where 
  visited : RBMap Name Bool compare

abbrev dfsM := ReaderT Graph $ EStateM String dfsState

open YatimaStdLib (Tree)

partial def generate (v : Vertex) : dfsM $ Tree Vertex := do
  match (← get).visited.find? v with
  | some _ => pure .empty
  | none => do
    set { ← get with visited := (← get).visited.insert v true }
    match (← read).find? v with 
    | some vs => do
      let ts ← vs.mapM generate
      pure $ .node v $ ts.filter $ not ∘ Tree.isEmpty
    | none => throw s!"Vertex {v} not found in graph"

def generateVs (vs : List Vertex) : dfsM $ List $ Tree Vertex := do 
  vs.mapM generate

def dfsM.run (g : Graph) (v : Vertex) : Except String $ Tree Vertex  :=
  match EStateM.run (ReaderT.run (generate v) g) { visited := .empty } with 
  | .ok res state => .ok res 
  | .error e _ => .error e

def dfs? (g : Graph) (vs : List Vertex) : Except String $ List $ Tree Vertex :=
  match EStateM.run (ReaderT.run (generateVs vs) g) { visited := .empty } with 
  | .ok res state => .ok res 
  | .error e _ => .error e

def dfs! (g : Graph) (vs : List Vertex) : List $ Tree Vertex :=
  match EStateM.run (ReaderT.run (generateVs vs) g) { visited := .empty } with 
  | .ok res state => res 
  | .error e _ => panic! e

def dff? (g : Graph) : Except String $ List $ Tree Vertex :=
  g.dfs? g.vertices 

def dff! (g : Graph) : List $ Tree Vertex :=
  g.dfs! g.vertices

def preord (g : Graph) : List Vertex :=
  Tree.preorderF g.dff!

def postord (g : Graph) : List Vertex :=
  Tree.postorderF (dff! g)

structure NodeInfo where
  index : Nat
  lowlink : Nat
  onStack : Bool
  deriving Repr

instance : ToString NodeInfo :=
  { toString := fun info => s!"i: {info.index}, low: {info.lowlink}, on: {info.onStack}" }

structure sccState where 
  info : RBMap Name NodeInfo compare
  index : Nat 
  stack : List Name

instance : Inhabited sccState := 
  { default := ⟨.empty, default, default⟩ }

abbrev sccM := ReaderT Graph $ EStateM String sccState

namespace sccM

def getInfo (v : Vertex) : sccM NodeInfo := do 
  (← get).info.findM v s!"Vertex {v} not found in graph" 

def setInfo (v : Vertex) (info : NodeInfo) : sccM Unit := do
  set { ← get with info := (← get).info.insert v info }

/--  
`strongConnect v` returns all the strongly connected components
of the graph `G` (encoded in the `ReaderT` of the `sccM` monad)
that can be found by depth first searching from `v`.

Note that `G` is not necessarily simple, i.e. it may have self loops,
and we consider those singletons as strongly connected to itself.
-/
partial def strongConnect (v : Vertex) : sccM (List $ List Vertex) := do 
  let idx := (← get).index
  set ({ info := (← get).info.insert v ⟨idx, idx, true⟩, 
         index := idx + 1, 
         stack := v :: (← get).stack } : sccState)
  
  let edges ← match (← read).find? v with 
              | some vs => pure vs
              | none => throw s!"Vertex {v} not found in graph"
  
  let mut sccs := []
  let mut vll := idx 
  for w in edges do 
    match (← get).info.find? w with 
    | some ⟨widx, wlowlink, won⟩ => do 
      if won then
        vll := min vll widx
    | none => do
      sccs := (← strongConnect w) ++ sccs
      let ⟨_, wlowlink, _⟩ ← getInfo w
      vll := min vll wlowlink

  setInfo v ⟨idx, vll, true⟩
  
  if idx == vll then do
    let s := (← get).stack
    let (scc, s) := s.splitAtP fun w => w != v 
    scc.forM fun w => do 
      let ⟨idx, lowlink, on⟩ ← getInfo w
      setInfo w ⟨idx, lowlink, false⟩
    set { ← get with stack := s } 
    -- if `scc` has length 1, check if `v` has a self-loop
    if scc.length >= 2 || scc.length == 1 && edges.contains v then 
      pure $ scc::sccs
    else
      pure $ sccs
  else pure sccs

def run : sccM $ List $ List Vertex := do 
  (← read).vertices.foldlM (init := []) $ fun acc v => do
    match (← get).info.find? v with 
    | some ⟨idx, _, _⟩ => pure acc 
    | none => 
    match ← strongConnect v with 
      | [] => pure $ acc
      | as => pure $ as ++ acc

end sccM

def scc? (g : Graph) : Except String $ List $ List Vertex :=
  match EStateM.run (ReaderT.run sccM.run g) default with 
  | .ok  res _ => .ok res 
  | .error e _ => .error e

def scc! (g : Graph) : List $ List Vertex :=
  match EStateM.run (ReaderT.run sccM.run g) default with 
  | .ok  res _ => res 
  | .error e _ => panic! e

end Graph