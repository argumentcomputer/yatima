import Lurk.Syntax.DSL 

open Lurk.Syntax AST DSL

def prog := ⟦
(LETREC
 ((|getelem| (LAMBDA (|xs| |n|) (IF (= |n| 0) (CAR |xs|) (|getelem| (CDR |xs|) (- |n| 1)))))
  (|drop| (LAMBDA (|n| |xs|) (IF (= |n| 0) |xs| (IF |xs| (|drop| (- |n| 1) (CDR |xs|)) |xs|))))
  (|str_mk| (LAMBDA (|cs|) (IF |cs| (STRCONS (CAR |cs|) (|str_mk| (CDR |cs|))) "")))
  (|str_data| (LAMBDA (|s|) (IF (EQ |s| "") NIL (CONS (CAR |s|) (|str_data| (CDR |s|))))))
  (|str_append| (LAMBDA (|xs| |ys|) (IF (EQ "" |xs|) |ys| (STRCONS (CAR |xs|) (|str_append| (CDR |xs|) |ys|)))))
  (|Nat.add| (LAMBDA (|a| |b|) (+ |a| |b|)))
  (|List| (LAMBDA (|α|) (QUOTE ("List" 1 0))))
  (|List.nil| (LAMBDA (|α|) (CONS "List" (CONS 0 (CONS |α| NIL)))))
  (|List.cons| (LAMBDA (|α| |head| |tail|) (CONS "List" (CONS 1 (CONS |α| (CONS |head| (CONS |tail| NIL)))))))
  (|list| (LET ((|_x.17| (|List.nil| "lcErasedType"))) |_x.17|))
  (|List.map|
   (LAMBDA
    (|α| |β| |f| |x.1|)
    (LET
     ((|_lurk_idx| (|getelem| |x.1| 1)) (|_lurk_args| (|drop| |x.1| 3)))
     (IF
      (= |_lurk_idx| 0)
      (LET ((|_x.29| (|List.nil| "lcErasedType"))) |_x.29|)
      (IF
       (= |_lurk_idx| 1)
       (LET
        ((|head.12| (|getelem| |_lurk_args| 0)) (|tail.13| (|getelem| |_lurk_args| 1)))
        (LET
         ((|_x.30| (|f| |head.12|)))
         (LET
          ((|_x.31| (|List.map| "lcErasedType" "lcErasedType" |f| |tail.13|)))
          (LET ((|_x.32| (|List.cons| "lcErasedType" |_x.30| |_x.31|))) |_x.32|))))
       NIL)))))
  (|listMap|
   (LET
    ((|_f.25| (LAMBDA (|x|) (+ |x| 1))))
    (LET ((|_x.26| |list|)) (LET ((|_x.27| (|List.map| "lcErasedType" "lcErasedType" |_f.25| |_x.26|))) |_x.27|)))))
 |listMap|)
⟧