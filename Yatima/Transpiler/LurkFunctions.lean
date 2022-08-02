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

#eval IO.println $ ⟦
  (letrec (
    (getelem $(getelem.2))
  ) (
    getelem ,(1 2 3) 1
  ))
⟧.pprint.pretty 50

end Lurk