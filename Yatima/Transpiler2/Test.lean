import Lean
-- import Lurk.Hashing.Encoding
import Yatima.Transpiler2.Compile
import Yatima.Transpiler2.Find
import Yatima.Typechecker.Typechecker

open Lean.Compiler.LCNF 

def passes : Array Pass := #[
  init,
  pullInstances,
  cse,
  simp,
  floatLetIn,
  findJoinPoints,
  pullFunDecls,
  reduceJpArity,
  /-
  We apply `implementedBy` replacements before `specialize` to ensure we specialize the replacement.
  One possible improvement is to perform only the replacements if the target declaration is a specialization target,
  and on phase 2 (aka mono) perform the remaining replacements.
  -/
  simp { etaPoly := true, inlinePartial := true, implementedBy := true } (occurrence := 1),
  eagerLambdaLifting,
  -- specialize,
  simp (occurrence := 2),
  cse (occurrence := 1),
  saveBase, -- End of base phase
  toMono,
  simp (occurrence := 3) (phase := .mono),
  -- reduceJpArity (phase := .mono),
  -- extendJoinPointContext (phase := .mono) (occurrence := 0),
  -- floatLetIn (phase := .mono) (occurrence := 1),
  -- reduceArity,
  -- commonJoinPointArgs,
  -- simp (occurrence := 4) (phase := .mono),
  -- floatLetIn (phase := .mono) (occurrence := 2),
  -- lambdaLifting,
  -- extendJoinPointContext (phase := .mono) (occurrence := 1),
  -- simp (occurrence := 5) (phase := .mono),
  -- cse (occurrence := 2) (phase := .mono),
  saveMono  -- End of mono phase
]

def hmm := [1, 2, 3, 4, 5].foldl (init := 0) (· + ·)
-- def hmm2 := [1, 2, 3, 4, 5].length

-- def f (n : Nat) : Nat := Id.run do 
--   let mut res := 0
--   for i in [0:n] do
--     res := res + i
--   res 

-- @[inline] def g (n : Nat) : StateM Nat Nat := do
--   for i in [0:n] do 
--     modify fun x => x + i
--   get

-- def g.run (n : Nat) := StateT.run (g n) 0

-- #eval find fun cinfo => return (`Id.instMonadId).isPrefixOf cinfo.name

-- #eval g.run 10

-- #print Id.instMonadId._lambda_6._cstage2
-- set_option trace.Compiler.pullInstances true
-- set_option trace.Compiler.cse true
-- set_option trace.Compiler.simp true
-- set_option trace.Compiler true
set_option trace.Compiler.result true
-- #eval Lean.Compiler.toDecl ``Yatima.Typechecker.eval
#eval Lean.Compiler.compileWithPasses #[``List.rec] passes