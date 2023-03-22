import Lurk.DSL
import Yatima.CodeGen.Override

/-!
# Helper Functions for the code generator

This file provides Lurk "standard library" functions needed to
generally needed to write Lurk code.
-/

namespace Lurk.Preloads

open Lurk Expr.DSL LDON.DSL DSL

def throw : Lean.Name × Expr := (`throw, ⟦
  (lambda (msg) (begin (emit msg) (nil))) -- invalid function call to simulate error
⟧)

def reverse_aux : Lean.Name × Expr := (`reverse_aux, ⟦
  (lambda (xs ys)
    (if xs
        (reverse_aux (cdr xs) (cons (car xs) ys))
        ys))
⟧)

def reverse : Lean.Name × Expr := (`reverse, ⟦
  (lambda (xs) (reverse_aux xs nil))
⟧)

def push : Lean.Name × Expr := (`push, ⟦
  (lambda (xs y) (
    if xs
      (cons (car xs) (push (cdr xs) y))
      (cons y nil)))
⟧)

def append : Lean.Name × Expr := (`append, ⟦
  (lambda (xs ys) (
    if xs
      (cons (car xs) (append (cdr xs) ys))
      ys))
⟧)

/-- Warning: if `i` is out of bounds, we push `x` to the back. -/
def set : Lean.Name × Expr := (`set, ⟦
  (lambda (xs i x)
    (if (= i 0)
        (cons x (cdr xs))
        (cons (car xs) (set (cdr xs) (- i 1) x))))
⟧)

def set! : Lean.Name × Expr := (`set!, ⟦
  (lambda (xs i x)
    (if (= i 0)
        (if xs
            (cons x (cdr xs))
            (throw "panic! in set!"))
        (cons (car xs) (set! (cdr xs) (- i 1) x))))
⟧)

def length : Lean.Name × Expr := (`length, ⟦
  (lambda (xs) (
    if xs
      (+ 1 (length (cdr xs)))
      0))
⟧)

def take : Lean.Name × Expr := (`take, ⟦
  (lambda (n xs) (
    if (= n 0)
      nil
      (if xs
        (cons (car xs) (take (- n 1) (cdr xs)))
        xs)
    )
  )
⟧)

def drop : Lean.Name × Expr := (`drop, ⟦
  (lambda (n xs)
    (if (= n 0)
      xs
      (if xs
        (drop (- n 1) (cdr xs))
        xs)))
⟧)

def getelem! : Lean.Name × Expr := (`getelem!, ⟦
  (lambda (xs n)
    (if (= n 0)
      (if xs
          (car xs)
          (throw "panic! in getelem!"))
      (getelem! (cdr xs) (- n 1))))
⟧)

def str_mk : Lean.Name × Expr := (`str_mk, ⟦
  (lambda (cs)
    (if cs
      (strcons (char (car cs)) (str_mk (cdr cs)))
      ""
    )
  )
⟧)

def str_data : Lean.Name × Expr := (`str_data, ⟦
  (lambda (s)
    (if (eq s "")
      nil
      (cons (num (car s)) (str_data (cdr s)))
    )
  )
⟧)

def str_push : Lean.Name × Expr := (`str_push, ⟦
  (lambda (xs y) 
    (if (eq xs "")
      (strcons (char y) "")
      (strcons (car xs) (str_push (cdr xs) y))))
⟧)

def str_append : Lean.Name × Expr := (`str_append, ⟦
  (lambda (xs ys)
    (if (eq "" xs)
      ys
      (strcons
        (car xs)
        (str_append (cdr xs) ys))))
⟧)

def to_bool : Lean.Name × Expr := (`to_bool, ⟦
  (lambda (x)
    (if x 1 0))
⟧)

-- TODO: We can't use any of these because they do not have
-- the expected lazy behavior; we would need to write an inliner.

def lor : Lean.Name × Expr := (`lor, ⟦
  (lambda (x y)
    (if x t y))
⟧)

def land : Lean.Name × Expr := (`land, ⟦
  (lambda (x y)
    (if x y nil))
⟧)

def lneq : Lean.Name × Expr := (`lneq, ⟦
  (lambda (x y) (if (eq x y) nil t))
⟧)

def lnot : Lean.Name × Expr := (`lnot, ⟦
  (lambda (x)
    (if x nil t))
⟧)

end Lurk.Preloads
