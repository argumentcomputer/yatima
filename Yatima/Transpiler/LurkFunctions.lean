import Lurk.Syntax.DSL
import Yatima.Datatypes.Lean

/-!
# Helper Functions for the Transpiler and Examples

This file provides all helper functions needed to construct Lurk functions
from Yatima expressions.

Currently, inductives encode three pieces of information.
1. The name of the inductive. This is not used anywhere in the transpiler,
    but is useful to keep around for humans to debug and identify objects.
2. The number of parameters. Used to generate projections.
3. The number of indices. Also used to generate projections.

This information is somewhat arbitrary. It's the bare minimum needed to
make things work. If there are better representations or we need more
metadata it should be freely changed.
-/

namespace Lurk

open Yatima Lurk.Syntax DSL

namespace Preloads

def append : Name × AST := (`append, ⟦
  (lambda (xs ys) (
    if xs
      (cons (car xs) (append (cdr xs) ys))
      ys
  ))
⟧)

def str_append : Name × AST := (`str_append, ⟦
  (lambda (xs ys)
    (if (eq "" xs)
      ys
      (strcons
        (car xs)
        (str_append (cdr xs) ys))))
⟧)

def length : Name × AST := (`length, ⟦
  (lambda (xs) (
    if xs
      (+ 1 (length (cdr xs)))
      0
  ))
⟧)

def take : Name × AST := (`take, ⟦
  (lambda (n xs) (
    if (= n 0)
      nil
      (if xs
        (cons (car xs) (take (- n 1) (cdr xs)))
        xs)
    )
  )
⟧)

def drop : Name × AST := (`drop, ⟦
  (lambda (n xs)
    (if (= n 0)
      xs
      (if xs
        (drop (- n 1) (cdr xs))
        xs)
    )
  )
⟧)

def getelem : Name × AST := (`getelem, ⟦
  (lambda (xs n)
    (if (= n 0)
      (car xs)
      (getelem (cdr xs) (- n 1))
    )
  )
⟧)

def str_mk : Name × AST := (`str_mk, ⟦
  (lambda (cs)
    (if cs
      (strcons (car cs) (str_mk (cdr cs)))
      ""
    )
  )
⟧)

def str_data : Name × AST := (`str_data, ⟦
  (lambda (s)
    (if (eq s "")
      nil
      (cons (car s) (str_data (cdr s)))
    )
  )
⟧)

end Preloads

namespace Overrides

/-!
It's important that all overrides match with existing Lean names, so using
double backticks here can help mitigate some error.
-/

def Nat : Name × AST := (``Nat, ⟦
  ,("Nat" 0 0)
⟧)

def NatZero : Name × AST := (``Nat.zero, ⟦
  0
⟧)

def NatSucc : Name × AST := (``Nat.succ, ⟦
  (lambda (n) (+ n 1))
⟧)

def NatRec : Name × AST := (``Nat.rec, ⟦
  (lambda (motive zero succ _t)
    (if (= _t 0)
     zero
     (succ (- _t 1) (Nat.rec motive zero succ (- _t 1)))))
⟧)

def NatAdd : Name × AST := (``Nat.add, ⟦
  (lambda (a b) (+ a b))
⟧)

def NatSub : Name × AST := (``Nat.sub, ⟦
  (lambda (a b)
    (if (< a b)
      0
      (- a b)))
⟧)

def NatMul : Name × AST := (``Nat.mul, ⟦
  (lambda (a b) (* a b))
⟧)

def NatDiv : Name × AST := (``Nat.div, ⟦
  (lambda (a b)
    (if (< a b)
      0
      -- TODO: we write `((Nat.div a) b)` as a hack,
      -- the elaborator is otherwise confused and tries to parse `Nat.div`
      -- as a `binop`.
      (+ 1 (Nat.div (- a b) b))))
⟧)

def NatMod : Name × AST := (``Nat.mod, ⟦
  (lambda (a b)
    (if (< a b)
      0
      -- TODO: we write `((Nat.div a) b)` as a hack,
      -- the elaborator is otherwise confused and tries to parse `Nat.div`
      -- as a `binop`.
      (+ 1 (Nat.div (- a b) b))))
⟧)

def NatDecLe : Name × AST := (``Nat.decLe, ⟦
  (lambda (a b)
    (if (<= a b)
      ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
      ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧)

def NatBeq : Name × AST := (``Nat.beq, ⟦
  (lambda (a b) (
    if (= a b)
      ,(("Bool" 0 0) 1)
      ,(("Bool" 0 0) 0)
  ))
⟧)

def Char : Name × AST := (``Char, ⟦
  ,("Char" 0 0)
⟧)

def CharMk : Name × AST := (``Char.mk, ⟦
  (lambda (val valid)
    (char (getelem (getelem val 2) 3)))
⟧)

def CharVal : Name × AST := (``Char.val, ⟦
  (lambda (self)
    (UInt32.mk (Fin.mk UInt32.size (num self) t)))
⟧)

def CharValid : Name × AST := (``Char.val, ⟦
  (lambda (self) t)
⟧)

def CharRec : Name × AST := (``Char.rec, ⟦
  (lambda (motive mk _t)
    (mk (num (UInt32.mk (Fin.mk UInt32.size n t)))))
⟧)

def List : Name × AST := (``List, ⟦
  (lambda (x) ,("List" 1 0))
⟧)

def ListNil : Name × AST := (``List.nil, ⟦
  (lambda (x) nil)
⟧)

def ListCons : Name × AST := (``List.cons, ⟦
  (lambda (x head tail) (cons head tail))
⟧)

def ListRec : Name × AST := (``List.rec, ⟦
  (lambda (x motive _nil _cons _t)
    (if _t
      (_cons (car _t) (cdr _t) (List.rec x motive _nil _cons (cdr _t)))
      _nil))
⟧)

def ListHasDecEq : Name × AST := (``List.hasDecEq, ⟦
  (lambda (α _inst a b)
    (if (eq a b)
      ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
      ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧)

def ListMap : Name × AST := (``List.map, ⟦
  (lambda (α β f xs)
    (if xs
      (cons (f (car xs)) (List.map α β f (cdr xs)))
      nil))
⟧)

def ListFoldl : Name × AST := (``List.foldl, ⟦
  (lambda (α β f init xs)
    (if xs
      (List.foldl α β f (f init (car xs)) (cdr xs))
      init))
⟧)

def String : Name × AST := (``String, ⟦
  ,("String" 0 0)
⟧)

def StringMk : Name × AST := (``String.mk, ⟦
  (lambda (data) (str_mk data))
⟧)

def StringData : Name × AST := (``String.data, ⟦
  (lambda (self) (str_data self))
⟧)

def StringRec : Name × AST := (``String.rec, ⟦
  (lambda (motive mk _t)
    (mk (str_data _t)))
⟧)

def StringAppend : Name × AST := (``String.append, ⟦
  (lambda (s₁ s₂) (str_append s₁ s₂))
⟧)

def StringDecEq : Name × AST := (``String.decEq, ⟦
  (lambda (s₁ s₂)
    (if (eq s₁ s₂)
      ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
      ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧)

end Lurk.Overrides
