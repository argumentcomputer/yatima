import Yatima.ForLurkRepo.DSL 

/-!

# Helper Functions for the Transpiler and Examples 

This file provides all helper functions needed to construct Lurk functions 
from Yatima expressions. We also provide some detailed examples of what 
transpiled output should look like. 

-/

namespace Lurk 

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

def Nat : Name × Expr := (``Nat, ⟦
  (cons "Nat" (cons 0 (cons 0 nil)))
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

def NatMul : Name × Expr := (``Nat.mul, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) (* _x_lurk_1 _x_lurk_2))
⟧)

def NatDiv : Name × Expr := (``Nat.div, ⟦
  (lambda (_x_lurk_1 _x_lurk_2) 
    (if (< _x_lurk_1 _x_lurk_2)
        0
        (+ (Nat_div (- _x_lurk_1 _x_lurk_2) _x_lurk_2) 1)))
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
      Bool_true
      Bool_false
  ))
⟧)

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

-- #eval IO.println $ 
--   Expr.mkMutualBlock [(`f, f), (`g, g)] |>.map fun (n, e) => (n, e.pprint false |>.pretty 50)

-- #eval IO.println $ ⟦
--   (letrec (
--     (mutual_fg $(mutual_fg.2))
--   ) (
--     (mutual_fg 0) 10 
--   ))
-- ⟧.pprint.pretty 50

end Lurk