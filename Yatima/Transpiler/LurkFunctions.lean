import Lurk.Syntax.DSL
import Yatima.Transpiler.Override

/-!
# Helper Functions for the Transpiler and Examples

This file provides Lurk "standard library" functions needed to 
generally needed to write Lurk code.
-/

namespace Lurk

open Lean Compiler.LCNF
open Lurk.Syntax AST DSL
open Yatima.Transpiler

instance [ToAST α] [ToAST β] : ToAST (α × β) where
  toAST x := ~[toAST x.1, toAST x.2]

namespace Preloads

def reverse_aux : Name × AST := (`reverse_aux, ⟦
  (lambda (xs ys) 
    (if xs
        (reverse_aux (cdr xs) (cons (car xs) ys))
        ys))
⟧)

def reverse : Name × AST := (`reverse, ⟦
  (lambda (xs) (reverse_aux xs nil))
⟧)

def push : Name × AST := (`push, ⟦
  (lambda (xs y) (
    if xs
      (cons (car xs) (push (cdr xs) y))
      (cons y nil)))
⟧)

def append : Name × AST := (`append, ⟦
  (lambda (xs ys) (
    if xs
      (cons (car xs) (append (cdr xs) ys))
      ys))
⟧)

/-- Warning: if `i` is out of bounds, we push `x` to the back. -/
def set : Name × AST := (`set, ⟦
  (lambda (xs i x)
    (if (= i 0)
        (cons x (cdr xs))    
        (cons (car xs) (set! (cdr xs) (- i 1) x))))
⟧)

def set! : Name × AST := (`set!, ⟦
  (lambda (xs i x)
    (if (= i 0)
        (if xs
            (cons x (cdr xs))
            ("panic!"))
        (cons (car xs) (set! (cdr xs) (- i 1) x))))
⟧)

def length : Name × AST := (`length, ⟦
  (lambda (xs) (
    if xs
      (+ 1 (length (cdr xs)))
      0))
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
        xs)))
⟧)

/-- Note: this will not fail and return `nil` if `n` is out of bounds -/
def getelem : Name × AST := (`getelem, ⟦
  (lambda (xs n)
    (if (= n 0)
      (car xs)
      (getelem (cdr xs) (- n 1))))
⟧)

def getelem! : Name × AST := (`getelem!, ⟦
  (lambda (xs n)
    (if (= n 0)
      (if xs
          (car xs)
          ("panic!"))
      (getelem (cdr xs) (- n 1))))
⟧)

def neq : Name × AST := (`neq, ⟦
  (lambda (x y) (if (eq x y) nil t))
⟧)

def str_mk : Name × AST := (`str_mk, ⟦
  (lambda (cs)
    (if cs
      (strcons (char (car cs)) (str_mk (cdr cs)))
      ""
    )
  )
⟧)

def str_data : Name × AST := (`str_data, ⟦
  (lambda (s)
    (if (eq s "")
      nil
      (cons (num (car s)) (str_data (cdr s)))
    )
  )
⟧)

def str_push : Name × AST := (`str_push, ⟦
  (lambda (xs y) (
    if xs
      (strcons (car xs) (push (cdr xs) y))
      (strcons (char y) nil)))
⟧)

def str_append : Name × AST := (`str_append, ⟦
  (lambda (xs ys)
    (if (eq "" xs)
      ys
      (strcons
        (car xs)
        (str_append (cdr xs) ys))))
⟧)

def to_bool : Name × AST := (`to_bool, ⟦
  (lambda (x) 
    (if x
        ,(("Bool" 0 0) 1)
        ,(("Bool" 0 0) 0)))
⟧)

-- TODO: We can't use any of these because they do not have
-- the expected lazy behavior; we would need to write an inliner.

def lor : Name × AST := (`lor, ⟦
  (lambda (x y) 
    (if x t y))
⟧)

def land : Name × AST := (`land, ⟦
  (lambda (x y) 
    (if x y nil))
⟧)

def lnot : Name × AST := (`lnot, ⟦
  (lambda (x) 
    (if x nil t))
⟧)

end Preloads

end Lurk
