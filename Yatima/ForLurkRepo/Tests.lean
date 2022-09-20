import Yatima.ForLurkRepo.DSL 

def isZeroProg := ⟦
(letrec
 ((getelem
   (lambda (xs n)
    (if (= n 0)
     (car xs)
     ((getelem (cdr xs)) (- n 1)))))
  (Nat (quote ("Nat" 0 0)))
  (Nat_zero 0)
  (Nat_succ (lambda (n) (+ n 1)))
  (Nat_rec
   (lambda (motive zero succ _t)
    (if (= _t 0)
     zero
     ((succ (- _t 1))
      ((((Nat_rec motive) zero) succ)
       (- _t 1))))))
  (Nat_add
   (lambda (_x_lurk_1 _x_lurk_2)
    (+ _x_lurk_1 _x_lurk_2)))
  (Nat_mul
   (lambda (_x_lurk_1 _x_lurk_2)
    (* _x_lurk_1 _x_lurk_2)))
  (Nat_casesOn
   (lambda (motive _t zero succ)
    ((((Nat_rec motive) zero)
      (lambda (n n_ih) (succ n)))
     _t)))
  (PUnit (cons "PUnit" (cons 0 (cons 0 nil))))
  (PUnit_rec
   (lambda (motive unit _t)
    (if (= (car (cdr _t)) 0)
     ((unit motive) unit)
     nil)))
  (PUnit_unit (cons PUnit (cons 0 nil)))
  (Unit_unit PUnit_unit)
  (isZero_match_1
   (lambda
    (motive _fun_discr__40__hyg_6_13 h_1 h_2)
    ((((Nat_casesOn (lambda (x) (motive x)))
       _fun_discr__40__hyg_6_13)
      (h_1 Unit_unit))
     (lambda (n__40__hyg_25)
      (h_2 n__40__hyg_25)))))
  (Unit PUnit)
  (Bool (cons "Bool" (cons 0 (cons 0 nil))))
  (Bool_rec
   (lambda (motive false true _t)
    (if (= (car (cdr _t)) 0)
     (((false motive) false) true)
     (if (= (car (cdr _t)) 1)
      (((true motive) false) true)
      nil))))
  (Bool_false (cons Bool (cons 0 nil)))
  (Bool_true (cons Bool (cons 1 nil)))
  (isZero
   (lambda (_fun_discr__40__hyg_6)
    ((((isZero_match_1
        (lambda (_fun_discr__40__hyg_6_13) Bool))
       _fun_discr__40__hyg_6)
      (lambda (_x) Bool_true))
     (lambda (n) Bool_false))))
  (isZero__cstage1
   (lambda (_fun_discr__40__hyg_6)
    ((((Nat_casesOn
        (lambda (x)
         ((lambda (_fun_discr__40__hyg_6_13) Bool)
          x)))
       _fun_discr__40__hyg_6)
      Bool_true)
     (lambda (n__40__hyg_25) Bool_false))))
  (isZero_match_1__cstage1
   (lambda
    (motive _fun_discr__40__hyg_6_13 h_1 h_2)
    ((((Nat_casesOn (lambda (x) (motive x)))
       _fun_discr__40__hyg_6_13)
      (h_1 PUnit_unit))
     (lambda (n__40__hyg_25)
      (h_2 n__40__hyg_25))))))
 (isZero 3))
⟧
