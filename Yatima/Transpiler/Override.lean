import Lean.Compiler.LCNF.Main
import Lurk.Syntax.ExprUtils
import Yatima.Transpiler.MoveToLurk

/-!
# Transpiler Overrides

The overriding system in the transpiler is the result of how the Lean compiler works.
The problem for us is that the Lean compiler will not generate `LCNF` code
for declarations that it can avoid generating code for. Specifically, Lean
does not generate code for:

1. All inductives and constructors. Inductives and constructors are the "primitive"
    objects in Lean, and they have special representations in memory determined by the
    `C/C++` runtime. This means that inductives and constructors have bare `C/C++`
    implementations that manage their memory, and there is no need for `LCNF` here. 
2. All declarations tagged `@[extern]`, since the compiler assumes that it will be 
    replaced with custom `C/C++` code anyway. `Nat.decLt` is a perfect example.
3. All declarations tagged with `@[macro_inline]`, since these will be inlined 
    immediately in the code generation phase. `ite` and `dite` are immediate examples.
4. All `match_<n>` declarations. e.g. stuff like `List.map.match_1`, etc.
5. All `.rec`, `.recOn`, and `.casesOn` declarations, since all of these are compiled 
    to `case` statements in LCNF.
6. Some weird rules for instances. TODO: I'm not exactly sure.

The first two points are the most important ones. 

The first point means that we must determine our own inductive representation and
write our own constructors. This creates a separation between how we handle
declarations and inductives.

The second point means that we must "override" some declarations with our own custom
implementation. These apply to `@[extern]` declarations, but also to objects that have 
a native runtime representation in `lurk`: `Nat`, `List`, and `Char` (and some more). 
It would be terrible if we represented `2` as `Nat.succ (Nat.succ Nat.zero)` instead 
of just `2` in `lurk`! Hence, we need to both override inductives and declarations.

This creates 4 classes of "declarations" that we may have to deal with:

1. Normal declarations
2. Normal inductives 
   ^^ these exist in `(← read).env`
  
3. Override declarations
4. Override inductives
   ^^ these exist in `(← read).overrides`

This file defines the datatypes that encode override information.

-/

namespace Yatima.Transpiler
open Lurk.Syntax AST DSL
open Lean Compiler.LCNF

/-- This holds the bare minimum amount of inductive 
  data needed by the transpiler to do its job. -/
structure InductiveData where
  name : Lean.Name
  params : Nat
  indices : Nat
  /-- A map from each constructor name to its index.
    Here because for some reason `Lean.ConstructorVal` 
    doesn't actually hold this information and we have 
    to manually extract it ourselves. -/
  ctors : Lean.NameMap Nat

/-- A declaration override (a.k.a. type #3 in our list at the top).
  Just contains the name and a predefined replacement `AST`. -/
structure Override.Decl where
  declName : Name
  decl : AST

inductive Override.Alt where
  | alt (cidx : Nat) (params : Array Name) (code : AST)
  | default (code : AST)

/-- A inductive override (a.k.a. type #4 in our list at the top). -/
structure Override.Inductive where
  indData : InductiveData
  ind : Override.Decl
  ctors : Array Override.Decl
  mkCases : (discr : AST) → (alts : Array Override.Alt) → Except String AST

inductive Override where
  | decl (decl : Override.Decl) : Override
  | ind (ind : Override.Inductive) : Override

def Override.name : Override → Name
  | .decl odecl => odecl.declName
  | .ind oind => oind.ind.declName

end Yatima.Transpiler
