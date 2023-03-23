import Lurk.DSL
import Yatima.CodeGen.Override

namespace Lurk.Overrides

open Lurk Expr.DSL LDON.DSL DSL
open Yatima.CodeGen

def ArrayInductiveData : InductiveData :=
  ⟨``Array, 0, 0, .ofList [(``Array.mk, 0)]⟩

def ArrayCore : Override.Decl := ⟨``Array, ⟦
  (lambda (x) ,("Array" 1 0))
⟧⟩

def Array.mk : Override.Decl := ⟨``Array.mk, ⟦
  (lambda (type data) data)
⟧⟩

def ArrayMkCases (discr : Expr) (alts : Array Override.Alt) : Except String Expr := do
  let #[.alt 0 params k] := alts |
    throw s!"ArrayMkCases assumes structures having only one alternative, and never produce `default` match, got\n {alts}"
  let #[data] := params |
    throw s!"`Array.mk` case expects exactly 1 param, got\n {params}"
  let data := data.toString false
  return .let data ⟦(Array.data $discr)⟧ k

/-- We'll keep `Array` isomorphic to `List` for now,
  but of course this is extremely inefficient. -/
protected def Array : Override := Override.ind
  ⟨ArrayInductiveData, ArrayCore, #[Array.mk], ArrayMkCases⟩

def Array.data : Override := Override.decl ⟨``Array.data, ⟦
  (lambda (self) self)
⟧⟩

def Array.mkEmpty : Override := Override.decl ⟨``Array.mkEmpty, ⟦
  (lambda (α c) (List.nil nil))
⟧⟩

def Array.size : Override := Override.decl ⟨``Array.size, ⟦
  (lambda (α a) (List.length α a))
⟧⟩

def Array.get : Override := Override.decl ⟨``Array.get, ⟦
  (lambda (α a i) (getelem! a i))
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

def Array.uget : Override := Override.decl ⟨``Array.uget, ⟦
  (lambda (α a i h) (getelem! a i))
⟧⟩

def Array.uset : Override := Override.decl ⟨``Array.uset, ⟦
  (lambda (α a i v h) (set a i v))
⟧⟩

def Array.swap : Override := Override.decl ⟨``Array.swap, ⟦
  (lambda (α a i j)
    (let ((v₁ (getelem! a i))
          (v₂ (getelem! a j))
          (a' (set a i v₂)))
        (set a' j v₁)))
⟧⟩

def Array.swap! : Override := Override.decl ⟨``Array.swap!, ⟦
  (lambda (α a i j)
    (let ((v₁ (getelem! a i))
          (v₂ (getelem! a j))
          (a' (set a i v₂)))
        (set a' j v₁)))
⟧⟩

def Array.pop : Override := Override.decl ⟨``Array.pop, ⟦
  (lambda (α a) (List.dropLast α a))
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
  Array.mkArray,
  Array.uget,
  Array.uset,
  Array.swap,
  Array.swap!,
  Array.pop
]

end Lurk.Overrides
