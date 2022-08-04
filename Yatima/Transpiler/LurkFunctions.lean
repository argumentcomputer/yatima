import Yatima.ForLurkRepo.DSL 

namespace Lurk 

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

def zero := (`zero, ⟦
  (lambda () (append ,(zero 0) nil))
⟧)

def succ := (`succ, ⟦
  (lambda (n) (append ,(succ 1) (cons n nil)))
⟧)

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

-- #eval IO.println $ ⟦
--   (letrec (
--     (mutual_fg $(mutual_fg.2))
--   ) (
--     (mutual_fg 0) 10 
--   ))
-- ⟧.pprint.pretty 50

end Lurk