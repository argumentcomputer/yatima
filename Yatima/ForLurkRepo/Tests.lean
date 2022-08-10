import Yatima.ForLurkRepo.DSL 

def isZeroProg := ⟦
(letrec
 ((getelem
   (lambda (xs n)
    (if (= n 0)
     (car xs)
     (getelem (cdr xs) (- n 1)))))
  (Nat (quote ("Nat" 0 0)))
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
  (Nat_zero (cons Nat 0))
  (Nat_succ
   (lambda (n) (cons Nat (cons 1 (cons n nil)))))
  (two (Nat_succ (Nat_succ Nat_zero)))
  (anotherTwo__cstage1 two)
  (Nat_casesOn
   (lambda (motive _t zero succ)
    (Nat_rec
     motive
     zero
     (lambda (n n_ih) (succ n))
     _t)))
  (PUnit (quote ("PUnit" 0 0)))
  (PUnit_rec
   (lambda (motive unit _t)
    (if (= (car (cdr _t)) 0)
     ((lambda (motive unit) unit) motive unit)
     nil)))
  (PUnit_unit (cons PUnit 0))
  (Unit_unit PUnit_unit)
  (toZero_match_1
   (lambda
    (motive _fun_discr__40__hyg_29_36 h_1 h_2)
    (Nat_casesOn
     (lambda (x) (motive x))
     _fun_discr__40__hyg_29_36
     (h_1 Unit_unit)
     (lambda (n__40__hyg_49)
      (h_2 n__40__hyg_49)))))
  (toZero__unsafe_rec
   (lambda (_fun_discr__40__hyg_29)
    (toZero_match_1
     (lambda (_fun_discr__40__hyg_29_36) Nat)
     _fun_discr__40__hyg_29
     (lambda (_x) Nat_zero)
     (lambda (n) (toZero__unsafe_rec n)))))
  (Unit PUnit)
  (toZero_match_1__cstage1
   (lambda
    (motive _fun_discr__40__hyg_29_36 h_1 h_2)
    (Nat_casesOn
     (lambda (x) (motive x))
     _fun_discr__40__hyg_29_36
     (h_1 PUnit_unit)
     (lambda (n__40__hyg_49)
      (h_2 n__40__hyg_49)))))
  (HAdd_hAdd
   (lambda (_1 _2 _3 self)
    (getelem
     (cdr (cdr self))
     (+
      (+
       (getelem (car self) 1)
       (getelem (car self) 2))
      0))))
  (HAdd (quote ("HAdd" 3 0)))
  (HAdd_rec
   (lambda (:1 :2 :3 motive mk _t)
    (if (= (car (cdr _t)) 0)
     ((lambda (:1 :2 :3 motive mk hAdd) (mk hAdd))
      :1
      :2
      :3
      motive
      mk
      (getelem (cdr (cdr _t)) 0))
     nil)))
  (HAdd_mk
   (lambda (:1 :2 :3 hAdd)
    (cons
     HAdd
     (cons
      0
      (cons
       :1
       (cons :2 (cons :3 (cons hAdd nil))))))))
  (Add_add
   (lambda (:1 self)
    (getelem
     (cdr (cdr self))
     (+
      (+
       (getelem (car self) 1)
       (getelem (car self) 2))
      0))))
  (instHAdd
   (lambda (:1 inst__40_Init_Prelude__hyg_2401)
    (HAdd_mk
     :1
     :1
     :1
     (lambda (a b)
      (Add_add
       :1
       inst__40_Init_Prelude__hyg_2401
       a
       b)))))
  (Add (quote ("Add" 1 0)))
  (Add_rec
   (lambda (:1 motive mk _t)
    (if (= (car (cdr _t)) 0)
     ((lambda (:1 motive mk add) (mk add))
      :1
      motive
      mk
      (getelem (cdr (cdr _t)) 0))
     nil)))
  (Add_mk
   (lambda (:1 add)
    (cons Add (cons 0 (cons :1 (cons add nil))))))
  (PProd (quote ("PProd" 2 0)))
  (PProd_rec
   (lambda (:1 :2 motive mk _t)
    (if (= (car (cdr _t)) 0)
     ((lambda (:1 :2 motive mk fst snd)
       (mk fst snd))
      :1
      :2
      motive
      mk
      (getelem (cdr (cdr _t)) 0)
      (getelem (cdr (cdr _t)) 1))
     nil)))
  (PProd_mk
   (lambda (:1 :2 fst snd)
    (cons
     PProd
     (cons
      0
      (cons
       :1
       (cons :2 (cons fst (cons snd nil))))))))
  (Nat_below
   (lambda (motive _t)
    (Nat_rec
     (lambda (_t) nil)
     PUnit
     (lambda (n n_ih)
      (PProd (PProd (motive n) n_ih) PUnit))
     _t)))
  (Nat_brecOn
   (lambda (motive _t F_1)
    (getelem
     (cdr
      (cdr
       (Nat_rec
        (lambda (_t)
         (PProd
          (motive _t)
          (Nat_below motive _t)))
        (PProd_mk
         (motive Nat_zero)
         PUnit
         (F_1 Nat_zero PUnit_unit)
         PUnit_unit)
        (lambda (n n_ih)
         (PProd_mk
          (motive (Nat_succ n))
          (PProd
           (PProd (motive n) (Nat_below motive n))
           PUnit)
          (F_1
           (Nat_succ n)
           (PProd_mk
            (PProd
             (motive n)
             (Nat_below motive n))
            PUnit
            n_ih
            PUnit_unit))
          (PProd_mk
           (PProd (motive n) (Nat_below motive n))
           PUnit
           n_ih
           PUnit_unit)))
        _t)))
     (+
      (+
       (getelem
        (car
         (Nat_rec
          (lambda (_t)
           (PProd
            (motive _t)
            (Nat_below motive _t)))
          (PProd_mk
           (motive Nat_zero)
           PUnit
           (F_1 Nat_zero PUnit_unit)
           PUnit_unit)
          (lambda (n n_ih)
           (PProd_mk
            (motive (Nat_succ n))
            (PProd
             (PProd
              (motive n)
              (Nat_below motive n))
             PUnit)
            (F_1
             (Nat_succ n)
             (PProd_mk
              (PProd
               (motive n)
               (Nat_below motive n))
              PUnit
              n_ih
              PUnit_unit))
            (PProd_mk
             (PProd
              (motive n)
              (Nat_below motive n))
             PUnit
             n_ih
             PUnit_unit)))
          _t))
        1)
       (getelem
        (car
         (Nat_rec
          (lambda (_t)
           (PProd
            (motive _t)
            (Nat_below motive _t)))
          (PProd_mk
           (motive Nat_zero)
           PUnit
           (F_1 Nat_zero PUnit_unit)
           PUnit_unit)
          (lambda (n n_ih)
           (PProd_mk
            (motive (Nat_succ n))
            (PProd
             (PProd
              (motive n)
              (Nat_below motive n))
             PUnit)
            (F_1
             (Nat_succ n)
             (PProd_mk
              (PProd
               (motive n)
               (Nat_below motive n))
              PUnit
              n_ih
              PUnit_unit))
            (PProd_mk
             (PProd
              (motive n)
              (Nat_below motive n))
             PUnit
             n_ih
             PUnit_unit)))
          _t))
        2))
      0))))
  (Nat_add_match_1
   (lambda
    (motive
     _fun_discr__40_Init_Prelude__hyg_2732_2745
     _fun_discr__40_Init_Prelude__hyg_2733_2746
     h_1
     h_2)
    (Nat_casesOn
     (lambda (x)
      (motive
       _fun_discr__40_Init_Prelude__hyg_2732_2745
       x))
     _fun_discr__40_Init_Prelude__hyg_2733_2746
     (h_1
      _fun_discr__40_Init_Prelude__hyg_2732_2745)
     (lambda (n__40_Init_Prelude__hyg_2765)
      (h_2
       _fun_discr__40_Init_Prelude__hyg_2732_2745
       n__40_Init_Prelude__hyg_2765)))))
  (PProd_fst
   (lambda (:1 :2 self)
    (getelem
     (cdr (cdr self))
     (+
      (+
       (getelem (car self) 1)
       (getelem (car self) 2))
      0))))
  (Nat_add
   (lambda
    (_fun_discr__40_Init_Prelude__hyg_2732
     _fun_discr__40_Init_Prelude__hyg_2733)
    (Nat_brecOn
     (lambda
      (_fun_discr__40_Init_Prelude__hyg_2733)
      nil)
     _fun_discr__40_Init_Prelude__hyg_2733
     (lambda
      (_fun_discr__40_Init_Prelude__hyg_2733
       f
       _fun_discr__40_Init_Prelude__hyg_2732)
      (Nat_add_match_1
       (lambda
        (_fun_discr__40_Init_Prelude__hyg_2732_2745
         _fun_discr__40_Init_Prelude__hyg_2733_2746)
        nil)
       _fun_discr__40_Init_Prelude__hyg_2732
       _fun_discr__40_Init_Prelude__hyg_2733
       (lambda (a x__40_Init_Prelude__hyg_2768) a)
       (lambda (a b x__40_Init_Prelude__hyg_2768)
        (Nat_succ
         (PProd_fst
          ((lambda
            (_fun_discr__40_Init_Prelude__hyg_2733)
            nil)
           b)
          (Nat_rec
           (lambda (_t) nil)
           PUnit
           (lambda (n n_ih)
            (PProd
             (PProd
              ((lambda
                (_fun_discr__40_Init_Prelude__hyg_2733)
                nil)
               n)
              n_ih)
             PUnit))
           b)
          (PProd_fst
           (PProd
            ((lambda
              (_fun_discr__40_Init_Prelude__hyg_2733)
              nil)
             b)
            (Nat_rec
             (lambda (_t) nil)
             PUnit
             (lambda (n n_ih)
              (PProd
               (PProd
                ((lambda
                  (_fun_discr__40_Init_Prelude__hyg_2733)
                  nil)
                 n)
                n_ih)
               PUnit))
             b))
           PUnit
           x__40_Init_Prelude__hyg_2768)
          a)))
       f))
     _fun_discr__40_Init_Prelude__hyg_2732)))
  (instAddNat (Add_mk Nat Nat_add))
  (four
   (HAdd_hAdd
    Nat
    Nat
    Nat
    (instHAdd Nat instAddNat)
    two
    two))
  (outParam (lambda (:1) :1))
  (Prod (quote ("Prod" 2 0)))
  (Prod_rec
   (lambda (:1 :2 motive mk _t)
    (if (= (car (cdr _t)) 0)
     ((lambda (:1 :2 motive mk fst snd)
       (mk fst snd))
      :1
      :2
      motive
      mk
      (getelem (cdr (cdr _t)) 0)
      (getelem (cdr (cdr _t)) 1))
     nil)))
  (Prod_mk
   (lambda (:1 :2 fst snd)
    (cons
     Prod
     (cons
      0
      (cons
       :1
       (cons :2 (cons fst (cons snd nil))))))))
  (one (Nat_succ Nat_zero))
  (pair (Prod_mk Nat Nat one two))
  (toZero
   (lambda (_fun_discr__40__hyg_29)
    (Nat_brecOn
     (lambda (_fun_discr__40__hyg_29) Nat)
     _fun_discr__40__hyg_29
     (lambda (_fun_discr__40__hyg_29 f)
      (toZero_match_1
       (lambda (_fun_discr__40__hyg_29_36) nil)
       _fun_discr__40__hyg_29
       (lambda (anonymous x__40__hyg_50)
        Nat_zero)
       (lambda (n x__40__hyg_50)
        (PProd_fst
         ((lambda (_fun_discr__40__hyg_29) Nat) n)
         (Nat_rec
          (lambda (_t) nil)
          PUnit
          (lambda (n n_ih)
           (PProd
            (PProd
             ((lambda (_fun_discr__40__hyg_29)
               Nat)
              n)
             n_ih)
            PUnit))
          n)
         (PProd_fst
          (PProd
           ((lambda (_fun_discr__40__hyg_29) Nat)
            n)
           (Nat_rec
            (lambda (_t) nil)
            PUnit
            (lambda (n n_ih)
             (PProd
              (PProd
               ((lambda (_fun_discr__40__hyg_29)
                 Nat)
                n)
               n_ih)
              PUnit))
            n))
          PUnit
          x__40__hyg_50)))
       f)))))
  (toZero__cstage1
   (lambda (_fun_discr__40__hyg_29)
    (Nat_casesOn
     (lambda (x)
      ((lambda (_fun_discr__40__hyg_29_36) Nat)
       x))
     _fun_discr__40__hyg_29
     0
     (lambda (n__40__hyg_49)
      (toZero n__40__hyg_49)))))
  (one__cstage1 1)
  (toZero__sunfold
   (lambda (_fun_discr__40__hyg_29)
    (toZero_match_1
     (lambda (_fun_discr__40__hyg_29_36) Nat)
     _fun_discr__40__hyg_29
     (lambda (_x) Nat_zero)
     (lambda (n) (toZero n)))))
  (pair__cstage1 (Prod_mk Nat Nat one two))
  (Prod_snd
   (lambda (:1 :2 self)
    (getelem
     (cdr (cdr self))
     (+
      (+
       (getelem (car self) 1)
       (getelem (car self) 2))
      1))))
  (anotherTwo (Prod_snd Nat Nat pair))
  (two__cstage1 2)
  (four__cstage1 (Nat_add two two)))
 (current-env))
⟧