import Yatima.ForLurkRepo.Printing 
import Yatima.ForLurkRepo.DSL
open Lurk 
def prog := ⟦
(letrec
 ((getelem
   (lambda
    (xs n)
      (if (= n 0) (car xs) (getelem (cdr xs) (- n 1)))))
  (lurk_string_mk
   (lambda
    (cs)
      (if cs
       (strcons (car cs) (lurk_string_mk (cdr cs)))
       "")))
  (lurk_string_data
   (lambda
    (s)
      (if (eq s "")
       nil
       (cons (car s) (lurk_string_data (cdr s))))))
  (Tree (lambda (α) (quote ("Tree" 1 0))))
  (Tree_empty
   (lambda
    (α)
      (cons (quote ("Tree" 1 0))
       (cons 0 (cons (cons α nil) (cons nil (cons nil nil)))))))
  (Tree_node
   (lambda
    (α x_5 x_6)
      (cons (quote ("Tree" 1 0))
       (cons 1
        (cons (cons α nil)
         (cons nil (cons (cons x_5 (cons x_6 nil)) nil)))))))
  (List_rec
   (lambda
    (_lurk_1 motive _nil _cons _t)
      (if _t
       (_cons
          (car _t)
          (cdr _t)
          (List_rec _lurk_1 motive _nil _cons (cdr _t)))
       _nil)))
  (__mutual___Tree_rec_Tree_rec_1
   (lambda
    (mutidx)
      (if (= mutidx 0)
       (lambda
        (α motive_1 motive_2 empty node _nil _cons _t)
          (if (= (car (cdr _t)) 0)
           (let
            ((_lurk_ctor_args (getelem (cdr (cdr _t)) 2)))
            empty)
           (if (= (car (cdr _t)) 1)
            (let
             ((_lurk_ctor_args (getelem (cdr (cdr _t)) 2))
              (x_5 (getelem _lurk_ctor_args 0))
              (x_6 (getelem _lurk_ctor_args 1)))
             (node
                x_5
                x_6
                (__mutual___Tree_rec_Tree_rec_1
                   1
                   α
                   motive_1
                   motive_2
                   empty
                   node
                   _nil
                   _cons
                   x_6)))
            nil)))
       (if (= mutidx 1)
        (lambda
         (α
          motive_1
          motive_2
          empty
          node
          _nil
          _cons
          _t)
           (if _t
            (let
             ((head (car _t))
              (tail (cdr _t)))
             (_cons
                head
                tail
                (List_rec α motive _nil _cons tail)))
            _nil))
        nil))))
  (Tree_rec (__mutual___Tree_rec_Tree_rec_1 0))
  (Tree_rec_1 (__mutual___Tree_rec_Tree_rec_1 1))
  (PUnit (quote ("PUnit" 0 0)))
  (PUnit_unit (cons (quote ("PUnit" 0 0)) (cons 0 nil)))
  (PUnit_rec
   (lambda
    (motive unit _t)
      (if (= (car (cdr _t)) 0)
       (let
        ((_lurk_ctor_args (getelem (cdr (cdr _t)) 2)))
        unit)
       nil)))
  (Tree_casesOn
   (lambda
    (α motive_1 _t empty node)
      (Tree_rec
         α
         motive_1
         (lambda (_t) PUnit)
         empty
         (lambda (x_5 x_6 x_7) (node x_5 x_6))
         PUnit_unit
         (lambda (head tail head_ih tail_ih) PUnit_unit)
         _t)))
  (Unit_unit PUnit_unit)
  (x_2
   (lambda
    (x_3 motive x_4 h_1 h_2)
      (Tree_casesOn
         x_3
         (lambda (x) (motive x))
         x_4
         (h_1 Unit_unit)
         (lambda (x_8 x_9) (h_2 x_8 x_9)))))
  (Nat (quote ("Nat" 0 0)))
  (OfNat_ofNat
   (lambda
    (α x_11 self)
      (getelem (getelem (cdr (cdr self)) 2) 0)))
  (OfNat (lambda (α x_11) (quote ("OfNat" 2 0))))
  (OfNat_mk
   (lambda
    (α x_11 ofNat)
      (cons (quote ("OfNat" 2 0))
       (cons 0
        (cons (cons α (cons x_11 nil))
         (cons nil (cons (cons ofNat nil) nil)))))))
  (OfNat_rec
   (lambda
    (α x_11 motive mk _t)
      (if (= (car (cdr _t)) 0)
       (let
        ((_lurk_ctor_args (getelem (cdr (cdr _t)) 2))
         (ofNat (getelem _lurk_ctor_args 0)))
        (mk ofNat))
       nil)))
  (instOfNatNat (lambda (n) (OfNat_mk Nat n n)))
  (HAdd_hAdd
   (lambda
    (α β γ self)
      (getelem (getelem (cdr (cdr self)) 2) 0)))
  (HAdd (lambda (α β γ) (quote ("HAdd" 3 0))))
  (HAdd_mk
   (lambda
    (α β γ hAdd)
      (cons (quote ("HAdd" 3 0))
       (cons 0
        (cons (cons α (cons β (cons γ nil)))
         (cons nil (cons (cons hAdd nil) nil)))))))
  (HAdd_rec
   (lambda
    (α β γ motive mk _t)
      (if (= (car (cdr _t)) 0)
       (let
        ((_lurk_ctor_args (getelem (cdr (cdr _t)) 2))
         (hAdd (getelem _lurk_ctor_args 0)))
        (mk hAdd))
       nil)))
  (Add_add
   (lambda
    (α self)
      (getelem (getelem (cdr (cdr self)) 2) 0)))
  (instHAdd
   (lambda
    (α x_13)
      (HAdd_mk
         α
         α
         α
         (lambda (a b) (Add_add α x_13 a b)))))
  (Add (lambda (α) (quote ("Add" 1 0))))
  (Add_mk
   (lambda
    (α add)
      (cons (quote ("Add" 1 0))
       (cons 0
        (cons (cons α nil)
         (cons nil (cons (cons add nil) nil)))))))
  (Add_rec
   (lambda
    (α motive mk _t)
      (if (= (car (cdr _t)) 0)
       (let
        ((_lurk_ctor_args (getelem (cdr (cdr _t)) 2))
         (add (getelem _lurk_ctor_args 0)))
        (mk add))
       nil)))
  (Nat_add
   (lambda (_x_lurk_1 _x_lurk_2) (+ _x_lurk_1 _x_lurk_2)))
  (instAddNat (Add_mk Nat Nat_add))
  (List_foldl
   (lambda
    (α β f init xs)
      (if xs
       (List_foldl α β f (f init (car xs)) (cdr xs))
       init)))
  (List_map
   (lambda
    (α β f xs)
      (if xs
       (cons (f (car xs)) (List_map α β f (cdr xs)))
       nil)))
  (Tree_size__unsafe_rec
   (lambda
    (α x_1)
      (x_2
         α
         (lambda (x_10) Nat)
         x_1
         (lambda (_x) 0)
         (lambda
          (x_12 ts)
            (+ 1
               (List_foldl
                  Nat
                  Nat
                  (lambda (x_14 x_15) (+ x_14 x_15))
                  0
                  (List_map
                     (Tree α)
                     Nat
                     (Tree_size__unsafe_rec α)
                     ts)))))))
  (Tree_size Tree_size__unsafe_rec)
  (List_nil (lambda (_lurk_1) nil))
  (tree
   (Tree_node
      Nat
      4
      (List_nil (Tree Nat))))
  (treeSize (Tree_size Nat tree)))
 treeSize)
⟧

#eval prog.pprint