import Lurk.Syntax.DSL

open Lurk.Syntax.DSL

def prog := ⟦
(LETREC
 ((GETELEM (LAMBDA (XS N) (IF (= N 0) (CAR XS) (GETELEM (CDR XS) (- N 1)))))
  (LURK_STRING_MK (LAMBDA (CS) (IF CS (STRCONS (CAR CS) (LURK_STRING_MK (CDR CS))) "")))
  (LURK_STRING_DATA (LAMBDA (S) (IF (EQ S "") NIL (CONS (CAR S) (LURK_STRING_DATA (CDR S))))))
  (|HAppend_hAppend| (LAMBDA (|α| |β| |γ| |self|) (GETELEM (GETELEM (CDR (CDR |self|)) 2) 0)))
  (|String| (QUOTE ("String" 0 0)))
  (|HAppend| (LAMBDA (|α| |β| |γ|) (QUOTE ("HAppend" 3 0))))
  (|HAppend_mk| (LAMBDA (|α| |β| |γ| |hAppend|) ((QUOTE ("HAppend" 3 0)) 0 (|α| |β| |γ|) NIL (|hAppend|))))
  (|HAppend_rec|
   (LAMBDA
    (|α| |β| |γ| |motive| |mk| _T)
    (IF
     (= (CAR (CDR t)) 0)
     (LET ((_lurk_ctor_args (GETELEM (CDR (CDR t)) 2)) (hAppend (GETELEM _LURK_CTOR_ARGS 0))) (|mk| |hAppend|))
     NIL)))
  (|Append_append| (LAMBDA (|α| |self|) (GETELEM (GETELEM (CDR (CDR |self|)) 2) 0)))
  (|instHAppend| (LAMBDA (|α| |x_1|) (|HAppend_mk| |α| |α| |α| (LAMBDA (|a| |b|) (|Append_append| |α| |x_1| |a| |b|)))))
  (|Append| (LAMBDA (|α|) (QUOTE ("Append" 1 0))))
  (|Append_mk| (LAMBDA (|α| |append|) ((QUOTE ("Append" 1 0)) 0 (|α|) NIL (|append|))))
  (|Append_rec|
   (LAMBDA
    (|α| |motive| |mk| _T)
    (IF
     (= (CAR (CDR t)) 0)
     (LET ((_lurk_ctor_args (GETELEM (CDR (CDR t)) 2)) (append (GETELEM _LURK_CTOR_ARGS 0))) (|mk| |append|))
     NIL)))
  (|String_rec| (LAMBDA (MOTIVE MK _T) (MK (LURK_STRING_DATA _T))))
  (|String_casesOn| (LAMBDA (|motive| _T |mk|) (|String_rec| |motive| (LAMBDA (|data|) (|mk| |data|)) _T)))
  (|String_mk| (LAMBDA (DATA) (LURK_STRING_MK DATA)))
  (|String_append_match_1|
   (LAMBDA
    (|motive| |x_4| |x_5| |h_1|)
    (|String_casesOn|
     (LAMBDA (|x|) (|motive| |x| |x_5|))
     |x_4|
     (LAMBDA
      (|x_6|)
      (|String_casesOn|
       (LAMBDA (|x|) (|motive| (|String_mk| |x_6|) |x|))
       |x_5|
       (LAMBDA (|x_7|) (|h_1| |x_6| |x_7|)))))))
  (|List| (LAMBDA (_LURK_1) (QUOTE ("List" 1 0))))
  (|Char| (QUOTE ("Char" 0 0)))
  (|List_rec|
   (LAMBDA
    (_LURK_1 MOTIVE _NIL _CONS _T)
    (IF _T (_CONS (CAR _T) (CDR _T) (|List_rec| _LURK_1 MOTIVE _NIL _CONS (CDR _T))) _NIL)))
  (|PProd| (LAMBDA (|α| |β|) (QUOTE ("PProd" 2 0))))
  (|PProd_mk| (LAMBDA (|α| |β| |fst| |snd|) ((QUOTE ("PProd" 2 0)) 0 (|α| |β|) NIL (|fst| |snd|))))
  (|PProd_rec|
   (LAMBDA
    (|α| |β| |motive| |mk| _T)
    (IF
     (= (CAR (CDR t)) 0)
     (LET
      ((_lurk_ctor_args (GETELEM (CDR (CDR t)) 2)) (fst (GETELEM _LURK_CTOR_ARGS 0)) (snd (GETELEM _LURK_CTOR_ARGS 1)))
      (|mk| |fst| |snd|))
     NIL)))
  (|PUnit| (QUOTE ("PUnit" 0 0)))
  (|PUnit_unit| (CONS (QUOTE ("PUnit" 0 0)) (CONS 0 NIL)))
  (|PUnit_rec|
   (LAMBDA
    (|motive| |unit| _T)
    (IF (= (CAR (CDR t)) 0) (LET ((_lurk_ctor_args (GETELEM (CDR (CDR t)) 2))) |unit|) NIL)))
  (|List_below|
   (LAMBDA
    (|α| |motive| _T)
    (|List_rec|
     |α|
     (LAMBDA (_T) NIL)
     |PUnit|
     (LAMBDA (|head| |tail| |tail_ih|) (|PProd| (|PProd| (|motive| |tail|) |tail_ih|) |PUnit|))
     _T)))
  (|List_nil| (LAMBDA (_LURK_1) NIL))
  (|List_cons| (LAMBDA (_LURK_1 HEAD TAIL) (CONS HEAD TAIL)))
  (|List_brecOn|
   (LAMBDA
    (|α| |motive| _T |F_1|)
    (GETELEM
     (GETELEM
      (CDR
       (CDR
        (|List_rec|
         |α|
         (LAMBDA (_T) (|PProd| (|motive| _T) (|List_below| |α| |motive| _T)))
         (|PProd_mk| (|motive| (|List_nil| |α|)) |PUnit| (|F_1| (|List_nil| |α|) |PUnit_unit|) |PUnit_unit|)
         (LAMBDA
          (|head| |tail| |tail_ih|)
          (|PProd_mk|
           (|motive| (|List_cons| |α| |head| |tail|))
           (|PProd| (|PProd| (|motive| |tail|) (|List_below| |α| |motive| |tail|)) |PUnit|)
           (|F_1|
            (|List_cons| |α| |head| |tail|)
            (|PProd_mk| (|PProd| (|motive| |tail|) (|List_below| |α| |motive| |tail|)) |PUnit| |tail_ih| |PUnit_unit|))
           (|PProd_mk| (|PProd| (|motive| |tail|) (|List_below| |α| |motive| |tail|)) |PUnit| |tail_ih| |PUnit_unit|)))
         _T)))
      2)
     0)))
  (|List_casesOn|
   (LAMBDA
    (|α| |motive| _T |nil| |cons|)
    (|List_rec| |α| |motive| |nil| (LAMBDA (|head| |tail| |tail_ih|) (|cons| |head| |tail|)) _T)))
  (|List_reverseAux_match_1|
   (LAMBDA
    (|α| |motive| |x_10| |x_11| |h_1| |h_2|)
    (|List_casesOn|
     |α|
     (LAMBDA (|x|) (|motive| |x| |x_11|))
     |x_10|
     (|h_1| |x_11|)
     (LAMBDA (|x_12| |x_13|) (|h_2| |x_12| |x_13| |x_11|)))))
  (|PProd_fst| (LAMBDA (|α| |β| |self|) (GETELEM (GETELEM (CDR (CDR |self|)) 2) 0)))
  (|List_append|
   (LAMBDA
    (|α| |x_8| |x_9|)
    (|List_brecOn|
     |α|
     (LAMBDA (|x_8|) NIL)
     |x_8|
     (LAMBDA
      (|x_8| |f| |x_9|)
      (|List_reverseAux_match_1|
       |α|
       (LAMBDA (|x_14| |x_15|) NIL)
       |x_8|
       |x_9|
       (LAMBDA (|r| |x_16|) |r|)
       (LAMBDA
        (|a| |l| |r| |x_16|)
        (|List_cons|
         |α|
         |a|
         (|PProd_fst|
          ((LAMBDA (|x_8|) NIL) |l|)
          (|List_rec|
           |α|
           (LAMBDA (_T) NIL)
           |PUnit|
           (LAMBDA (|head| |tail| |tail_ih|) (|PProd| (|PProd| ((LAMBDA (|x_8|) NIL) |tail|) |tail_ih|) |PUnit|))
           |l|)
          (|PProd_fst|
           (|PProd|
            ((LAMBDA (|x_8|) NIL) |l|)
            (|List_rec|
             |α|
             (LAMBDA (_T) NIL)
             |PUnit|
             (LAMBDA (|head| |tail| |tail_ih|) (|PProd| (|PProd| ((LAMBDA (|x_8|) NIL) |tail|) |tail_ih|) |PUnit|))
             |l|))
           |PUnit|
           |x_16|)
          |r|)))
       |f|))
     |x_9|)))
  (|List_instAppendList| (LAMBDA (|α|) (|Append_mk| (|List| |α|) (|List_append| |α|))))
  (|String_append|
   (LAMBDA
    (|x_2| |x_3|)
    (|String_append_match_1|
     (LAMBDA (|x_4| |x_5|) |String|)
     |x_2|
     |x_3|
     (LAMBDA
      (|a| |b|)
      (|String_mk|
       (|HAppend_hAppend|
        (|List| |Char|)
        (|List| |Char|)
        (|List| |Char|)
        (|instHAppend| (|List| |Char|) (|List_instAppendList| |Char|))
        |a|
        |b|))))))
  (|String_instAppendString| (|Append_mk| |String| |String_append|))
  (|strAppend|
   (|HAppend_hAppend| |String| |String| |String| (|instHAppend| |String| |String_instAppendString|) "abc" "efg")))
 |strAppend|)
⟧