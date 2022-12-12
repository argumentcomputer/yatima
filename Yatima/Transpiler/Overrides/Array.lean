import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

namespace Overrides

def ArrayInductiveData : InductiveData :=
  ⟨``Array, 0, 0, .ofList [(``Array.mk, 0)]⟩

def ArrayCore : Override.Decl := ⟨``Array, ⟦
  (lambda (x) ,("Array" 1 0))
⟧⟩

def Array.mk : Override.Decl := ⟨``Array.mk, ⟦
  (lambda (data) data)
⟧⟩

def ArrayMkCases (discr : AST) (alts : Array Override.Alt) : Except String AST := do
  let #[.alt 0 params k] := alts |
    throw "we assume that structures only have one alternative, and never produce `default` match cases"
  let #[data] := params |
    throw s!"`Array.mk` case expects exactly 1 param, got\n {params}"
  return ⟦(let (($data (Array.data $discr))) $k)⟧

/-- We'll keep `Array` isomorphic to `List` for now, 
  but of course this is extremely inefficient. -/
protected def Array : Override := Override.ind
  ⟨ArrayInductiveData, ArrayCore, #[Array.mk], ArrayMkCases⟩

def Array.data : Override := Override.decl ⟨``Array.data, ⟦
  (lambda (self) self)
⟧⟩

def Array.mkEmpty : Override := Override.decl ⟨``Array.mkEmpty, ⟦
  (lambda (α c) (List.nil "lcErased"))
⟧⟩

def Array.size : Override := Override.decl ⟨``Array.size, ⟦
  (lambda (α a) (List.length α a))
⟧⟩

def Array.get : Override := Override.decl ⟨``Array.get, ⟦
  (lambda (α a i) (getelem a i))
⟧⟩

def Array.get! : Override := Override.decl ⟨``Array.get!, ⟦
  (lambda (α inst a i) (getelem! a i))
⟧⟩

/-- Warning: this is `O(n)` and extremely inefficient. -/
def Array.push : Override := Override.decl ⟨``Array.push, ⟦
  (lambda (α a v) (push a v))
⟧⟩

def Array.set : Override := Override.decl ⟨``Array.set, ⟦
  (lambda (α a i v) (set a i v))
⟧⟩

def Array.set! : Override := Override.decl ⟨``Array.set!, ⟦
  (lambda (α a i v) (set! a i v))
⟧⟩

def Array.mkArray : Override := Override.decl ⟨``Array.mkArray, ⟦
  (lambda (α n v) (List.replicate α n v))
⟧⟩

def Array.module : List Override := [
  Lurk.Overrides.Array, 
  Array.data,
  Array.mkEmpty,
  Array.size,
  Array.get,
  Array.get!,
  Array.push,
  Array.set,
  Array.set!,
  Array.mkArray
]

end Overrides

end Lurk