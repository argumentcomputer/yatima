import Lurk.Syntax.DSL
import Yatima.Datatypes.Lean

/-!
# Helper Functions for the Transpiler and Examples 

This file provides all helper functions needed to construct Lurk functions 
from Yatima expressions. We also provide some detailed examples of what 
transpiled output should look like. 

-/

namespace Lurk.Functions

open Yatima Lurk.Syntax DSL

/-! 
## Helper Functions 
Technically only `getelem` is used right now, but maybe the others will find use.
-/

def hmm := ⟦(LAMBDA (|α| |append|) ((QUOTE ("Append" 1 0)) 0 (|α|) |NIL| (|append|)))⟧
#print Append.mk
def append : Name × AST := (`APPEND, ⟦
  (lambda (xs ys) (
    if xs
      (cons (car xs) (append (cdr xs) ys))
      ys
  ))
⟧) 

def length : Name × AST := (`LENGTH, ⟦
  (lambda (xs) (
    if xs (
      + 1 (length (cdr xs))
    ) 0
  ))
⟧)

def take : Name × AST := (`TAKE, ⟦
  (lambda (n xs) (
    if (= n 0) 
    nil (
      if xs (
        cons (car xs) (take (- n 1) (cdr xs)) 
      ) xs
    )
  ))
⟧)

def drop : Name × AST := (`DROP, ⟦
  (lambda (n xs) (
    if (= n 0) 
      xs
    (
      if xs (
        drop (- n 1) (cdr xs)
      ) xs
    )
  ))
⟧)

def getelem : Name × AST := (`getelem, ⟦
  (lambda (xs n) (
    if (= n 0) (
      car xs
    ) (
      $(`getelem) (cdr xs) (- n 1)
    )
  ))
⟧)

def lurk_string_mk : Name × AST := (`LURK_STRING_MK, ⟦
  (lambda (cs) 
    (if cs 
      (strcons (car cs) (lurk_string_mk (cdr cs))) 
      ""))
⟧)

def lurk_string_data : Name × AST := (`LURK_STRING_DATA, ⟦
  (lambda (s) 
    (if (eq s "") 
      nil
      (cons (car s) (lurk_string_data (cdr s)))))
⟧)

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
     (succ (- _t 1) (|Nat.rec| motive zero succ (- _t 1)))))
⟧)

def NatAdd : Name × AST := (``Nat.add, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) (+ _x_lurk_1 _x_lurk_2))
⟧)

def NatSub : Name × AST := (``Nat.sub, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (< _x_lurk_1 _x_lurk_2)
        0
        (- _x_lurk_1 _x_lurk_2)))
⟧)

def NatMul : Name × AST := (``Nat.mul, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) (* _x_lurk_1 _x_lurk_2))
⟧)

def NatDiv : Name × AST := (``Nat.div, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (< _x_lurk_1 _x_lurk_2)
        0
        -- TODO: we write `((Nat.div x_1) x_2)` as a hack, 
        -- the elaborator is otherwise confused and tries to parse `Nat.div`
        -- as a `binop`. 
        (+ 1 (|Nat.div| (- _x_lurk_1 _x_lurk_2) _x_lurk_2))))
⟧)

def NatMod : Name × AST := (``Nat.mod, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (< _x_lurk_1 _x_lurk_2)
        0
        -- TODO: we write `((Nat.div x_1) x_2)` as a hack, 
        -- the elaborator is otherwise confused and tries to parse `Nat.div`
        -- as a `binop`. 
        (+ 1 (|Nat.div| (- _x_lurk_1 _x_lurk_2) _x_lurk_2))))
⟧)

def NatDecLe : Name × AST := (``Nat.decLe, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (<= _x_lurk_1 _x_lurk_2)
        ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
        ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧)

-- doesn't quite work yet because depends on `Bool`
def NatBeq : Name × AST := (``Nat.beq, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) (
    if (= _x_lurk_1 _x_lurk_2) 
      |Bool.true|
      |Bool.false|
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
    (|UInt32.mk| (|Fin.mk| |UInt32.size| (num self) t)))
⟧)

def CharValid : Name × AST := (``Char.val, ⟦
  (lambda (self) t)
⟧)

def CharRec : Name × AST := (``Char.rec, ⟦
  (lambda (motive mk _t) 
    (mk (num (|UInt32.mk| (|Fin.mk| |UInt32.size| n t)))))
⟧)

def List : Name × AST := (``List, ⟦
  (lambda (_lurk_1) ,("List" 1 0))
⟧)

def ListNil : Name × AST := (``List.nil, ⟦
  (lambda (_lurk_1) nil)
⟧)

def ListCons : Name × AST := (``List.cons, ⟦
  (lambda (_lurk_1 head tail) (cons head tail))
⟧)

def ListRec : Name × AST := (``List.rec, ⟦
  (lambda (_lurk_1 motive _nil _cons _t)
    (if _t
     (_cons (car _t) (cdr _t) (|List.rec| _lurk_1 motive _nil _cons (cdr _t)))
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
        (cons (f (car xs)) (|List.map| α β f (cdr xs)))
        nil))
⟧)

def ListFoldl : Name × AST := (``List.foldl, ⟦
  (lambda (α β f init xs) 
    (if xs
        (|List.foldl| α β f (f init (car xs)) (cdr xs))
        init))
⟧)

def String : Name × AST := (``String, ⟦
  ,("String" 0 0)
⟧)

def StringMk : Name × AST := (``String.mk, ⟦
  (lambda (data) (lurk_string_mk data))
⟧)

def StringData : Name × AST := (``String.data, ⟦
  (lambda (self) (lurk_string_data self))
⟧)

def StringRec : Name × AST := (``String.rec, ⟦
  (lambda (motive mk _t) 
    (mk (lurk_string_data _t)))
⟧)

def StringDecEq : Name × AST := (``String.decEq, ⟦
  (lambda (s₁ s₂) 
    (if (eq s₁ s₂)
        ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
        ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧)

namespace Example

/-! 
## `Nat` Example
-/

/-- The Lurk definition of `Nat`.
  Currently, inductives encode three pieces of information.
  1. The name of the inductive. This is not used anywhere in the transpiler, 
     but is useful to keep around for humans to debug and identify objects.
  2. The number of parameters. Used to generate projections.
  3. The number of indices. Also used to generate projections.
  
  This information is somewhat arbitrary. It's the bare minimum needed to
  make things work. If there are better representations or we need more 
  metadata it should be freely changed. -/
def nat := (`nat, ⟦
  ,("Nat" 0 0)
⟧)

-- def zero := (`zero, ⟦
--   (lambda () (append ,(zero 0) nil))
-- ⟧)

-- def succ := (`succ, ⟦
--   (lambda (n) (append ,(succ 1) (cons n nil)))
-- ⟧)

def mutual_fg := (`f_mutual, ⟦
  (lambda (n) (
    if (= n 0) (
      lambda (x) (
        if (= x 0) 0 (
          + ((mutual_fg 1) (- x 1)) 2
        )
      )
    ) (
      lambda (x) (
        if (= x 0) 0 (
          + ((mutual_fg 0) (- x 1)) 2
        )
      )
    )
  ))
⟧)

def f := ⟦(
  lambda (x) (
    if (= x 0) 0 (
      + (g (- x 1)) 2
    )
  )
)⟧

def g := ⟦(
  lambda (x) (
    if (= x 0) 0 (
      + (f (- x 1)) 2
    )
  )
)⟧

end Example

end Lurk.Functions
