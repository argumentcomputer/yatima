import Yatima.ForLurkRepo.DSL 

namespace Lurk 

def append : Name × Expr := (`lurk_append, ⟦
  (lambda (xs ys) (
    if xs
      (cons (car xs) (lurk_append (cdr xs) ys))
      ys
  ))
⟧) 

def length : Name × Expr := (`lurk_length, ⟦
  (lambda (xs) (
    if xs (
      + 1 (lurk_length (cdr xs))
    ) 0
  ))
⟧)

def take : Name × Expr := (`lurk_take, ⟦
  (lambda (n xs) (
    if (= n 0) 
    () (
      if xs (
        cons (car xs) (lurk_take (- n 1) (cdr xs)) 
      ) xs
    )
  ))
⟧)

def drop : Name × Expr := (`lurk_drop, ⟦
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

def zero := (`zero, ⟦
  (lambda () (append ,(zero 0) nil))
⟧)

def succ := (`succ, ⟦
  (lambda (n) (append ,(succ 1) (cons n nil)))
⟧)

#eval IO.println $ ⟦
  (letrec (
    (append $(append.2))
    (zero $(zero.2)) 
    (succ $(succ.2))
  ) (
    cdr (cdr (succ (succ (zero))))
  ))
⟧.pprint.pretty 50

end Lurk