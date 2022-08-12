import Yatima.ForLurkRepo.DSL 

def isZeroProg := ⟦
(letrec
 ((append
   (lambda (xs ys)
    (if xs
     (cons (car xs) (append (cdr xs) ys))
     ys)))
  (getelem
   (lambda (xs n)
    (if (= n 0)
     (car xs)
     (getelem (cdr xs) (- n 1)))))
  (Nat nil)
  (Nat_zero (quote ("Nat.zero" 0)))
  (Nat_succ
   (lambda (n)
    (append (quote ("Nat.succ" 1)) (cons n nil))))
  (Nat_rec
   (lambda (motive zero succ _t)
    (if (= (car (cdr _t)) 0)
     ((lambda (motive zero succ) zero)
      motive
      zero
      succ)
     (if (= (car (cdr _t)) 1)
      ((lambda (motive zero succ n)
        (succ n (Nat_rec motive zero succ n)))
       motive
       zero
       succ
       (getelem (cdr (cdr _t)) 0))
      nil))))
  (Bool nil)
  (Bool_false (quote ("Bool.false" 0)))
  (Bool_true (quote ("Bool.true" 1))))
 (Nat_rec
    (lambda (x) Bool)
    Bool_true
    (lambda (x ih) Bool_false)
    Nat_zero))
⟧