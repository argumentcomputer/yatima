import Lurk.Syntax.DSL

/-!

# Helper Functions for the Transpiler and Examples 

This file provides all helper functions needed to construct Lurk functions 
from Yatima expressions. We also provide some detailed examples of what 
transpiled output should look like. 

-/

namespace Lurk.Functions

open Lurk.Syntax

open Syntax DSL SExpr.DSL

/-! 
## Helper Functions 
Technically only `getelem` is used right now, but maybe the others will find use.
-/

def append : Name × Expr := (`append, ⟦
  (lambda (xs ys) (
    if xs
      (cons (car xs) (append (cdr xs) ys))
      ys
  ))
⟧) 

def length : Name × Expr := (`length, ⟦
  (lambda (xs) (
    if xs (
      + 1 (length (cdr xs))
    ) 0
  ))
⟧)

def take : Name × Expr := (`take, ⟦
  (lambda (n xs) (
    if (= n 0) 
    nil (
      if xs (
        cons (car xs) (take (- n 1) (cdr xs)) 
      ) xs
    )
  ))
⟧)

def drop : Name × Expr := (`drop, ⟦
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

def getelem : Name × Expr := (`getelem, ⟦
  (lambda (xs n) (
    if (= n 0) (
      car xs
    ) (
      getelem (cdr xs) (- n 1)
    )
  ))
⟧)

def lurk_string_mk : Name × Expr := (`lurk_string_mk, ⟦
  (lambda (cs) 
    (if cs 
      (strcons (car cs) (lurk_string_mk (cdr cs))) 
      ""))
⟧)

def lurk_string_data : Name × Expr := (`lurk_string_data, ⟦
  (lambda (s) 
    (if (eq s "") 
      nil
      (cons (car s) (lurk_string_data (cdr s)))))
⟧)

def Nat : Name × Expr := (``Nat, ⟦
  ,("Nat" 0 0)
⟧)

def NatZero : Name × Expr := (``Nat.zero, ⟦
  0
⟧)

def NatSucc : Name × Expr := (``Nat.succ, ⟦
  (lambda (n) (+ n 1))
⟧)

def NatRec : Name × Expr := (``Nat.rec, ⟦
  (lambda (motive zero succ _t)
    (if (= _t 0)
     zero
     (succ (- _t 1) ($(``Nat.rec) motive zero succ (- _t 1)))))
⟧)

def NatAdd : Name × Expr := (``Nat.add, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) (+ _x_lurk_1 _x_lurk_2))
⟧)

def NatSub : Name × Expr := (``Nat.sub, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (< _x_lurk_1 _x_lurk_2)
        0
        (- _x_lurk_1 _x_lurk_2)))
⟧)

def NatMul : Name × Expr := (``Nat.mul, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) (* _x_lurk_1 _x_lurk_2))
⟧)

def NatDiv : Name × Expr := (``Nat.div, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (< _x_lurk_1 _x_lurk_2)
        0
        -- TODO: we write `((Nat.div x_1) x_2)` as a hack, 
        -- the elaborator is otherwise confused and tries to parse `Nat.div`
        -- as a `binop`. 
        (+ 1 (($(``Nat.div) (- _x_lurk_1 _x_lurk_2)) _x_lurk_2))))
⟧)

def NatMod : Name × Expr := (``Nat.mod, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (< _x_lurk_1 _x_lurk_2)
        0
        -- TODO: we write `((Nat.div x_1) x_2)` as a hack, 
        -- the elaborator is otherwise confused and tries to parse `Nat.div`
        -- as a `binop`. 
        (+ 1 (($(``Nat.div) (- _x_lurk_1 _x_lurk_2)) _x_lurk_2))))
⟧)

def NatDecLe : Name × Expr := (``Nat.decLe, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (<= _x_lurk_1 _x_lurk_2)
        ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
        ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧)

-- doesn't quite work yet because depends on `Bool`
def NatBeq : Name × Expr := (``Nat.beq, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) (
    if (= _x_lurk_1 _x_lurk_2) 
      $(``true)
      $(``false)
  ))
⟧)

def Char : Name × Expr := (``Char, ⟦
  ,("Char" 0 0)
⟧)

def CharMk : Name × Expr := (``Char.mk, ⟦
  (lambda (val valid) 
    (char (getelem (getelem val 2) 3)))
⟧)

def CharVal : Name × Expr := (``Char.val, ⟦
  (lambda (self) 
    ($(``UInt32.mk) ($(``Fin.mk) $(``UInt32.size) (num self) t)))
⟧)

def CharValid : Name × Expr := (``Char.val, ⟦
  (lambda (self) t)
⟧)

def CharRec : Name × Expr := (``Char.rec, ⟦
  (lambda (motive mk _t) 
    (mk (num ($(``UInt32.mk) ($(``Fin.mk) $(``UInt32.size) n t)))))
⟧)

def List : Name × Expr := (``List, ⟦
  (lambda (_lurk_1) (quote ("List" 1 0)))
⟧)

def ListNil : Name × Expr := (``List.nil, ⟦
  (lambda (_lurk_1) nil)
⟧)

def ListCons : Name × Expr := (``List.cons, ⟦
  (lambda (_lurk_1 head tail) (cons head tail))
⟧)

def ListRec : Name × Expr := (``List.rec, ⟦
  (lambda (_lurk_1 motive _nil _cons _t)
    (if _t
     (_cons (car _t) (cdr _t) ($(``List.rec) _lurk_1 motive _nil _cons (cdr _t)))
     _nil))
⟧)

def ListHasDecEq : Name × Expr := (``List.hasDecEq, ⟦
  (lambda (α _inst a b) 
    (if (eq a b)
        ,(("Decidable" 1 0) 1 ("Nat.le" 1 1) t)
        ,(("Decidable" 1 0) 0 ("Nat.le" 1 1) t)))
⟧)

def ListMap : Name × Expr := (``List.map, ⟦
  (lambda (α β f xs) 
    (if xs
        (cons (f (car xs)) ($(``List.map) α β f (cdr xs)))
        nil))
⟧)

def ListFoldl : Name × Expr := (``List.foldl, ⟦
  (lambda (α β f init xs) 
    (if xs
        ($(``List.foldl) α β f (f init (car xs)) (cdr xs))
        init))
⟧)

def String : Name × Expr := (``String, ⟦
  ,("String" 0 0)
⟧)

def StringMk : Name × Expr := (``String.mk, ⟦
  (lambda (data) (lurk_string_mk data))
⟧)

def StringData : Name × Expr := (``String.data, ⟦
  (lambda (self) (lurk_string_data self))
⟧)

def StringRec : Name × Expr := (``String.rec, ⟦
  (lambda (motive mk _t) 
    (mk (lurk_string_data _t)))
⟧)

def StringDecEq : Name × Expr := (``String.decEq, ⟦
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
