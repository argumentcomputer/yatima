import Yatima.ForLurkRepo.Eval
open Lurk 

instance {n : Nat} : OfNat Value n where 
  ofNat := .lit $ .num $ Fin.ofNat n

abbrev Lurk.Test := Except String Value × Expr 

def outer_evaluate : Test := (.ok 99, ⟦((lambda (x) x) 99)⟧)

def outer_evaluate2 : Test := (.ok 99, ⟦
  ((lambda (y)
     ((lambda (x) y) 888))
   99)
⟧)

def outer_evaluate3 : Test := (.ok 999, ⟦
  ((lambda (y)
    ((lambda (x)
        ((lambda (z) z)
        x))
      y))
  999)
⟧)

def outer_evaluate4 : Test := (.ok 888, ⟦
  ((lambda (y)
      ((lambda (x)
          ((lambda (z) z)
          x))
        -- NOTE: We pass a different value here.
        888))
    999)
⟧)

def outer_evaluate5 : Test := (.ok 999, ⟦
  (((lambda (fn)
        (lambda (x) (fn x)))
      (lambda (y) y))
    999)
⟧)

def outer_evaluate_sum : Test := (.ok 9, ⟦(+ 2 (+ 3 4))⟧)

def outer_evaluate_diff : Test := (.ok 4, ⟦(- 9 5)⟧)

def outer_evaluate_product : Test := (.ok 45, ⟦(* 9 5)⟧)

def outer_evaluate_quotient : Test :=
(.ok 3, ⟦(/ 21 7)⟧)

def outer_evaluate_num_equal_1 : Test :=
(.ok TRUE, ⟦(= 5 5)⟧)

def outer_evaluate_num_equal_2 : Test :=
(.ok FALSE, ⟦(= 5 6)⟧)

def outer_evaluate_adder : Test :=
(.ok 5, ⟦(((lambda (x)
                   (lambda (y)
                     (+ x y)))
                 2)
                3)⟧)

def outer_evaluate_let_simple : Test :=
(.ok 1, ⟦(let ((a 1))
                 a)⟧)

def outer_evaluate_let_bug : Test :=
(.ok (.cons 1 2), ⟦(let () (cons 1 2))⟧)

def outer_evaluate_let : Test :=
(.ok 6, ⟦(let ((a 1)
                      (b 2)
                      (c 3))
                 (+ a (+ b c)))⟧)

def outer_evaluate_arithmetic : Test :=
(.ok 20, ⟦((((lambda (x)
                     (lambda (y)
                       (lambda (z)
                         (* z
                            (+ x y)))))
                   2)
                  3)
                 4)⟧)

-- NOTE: I think this test has drifted and is defunct.
-- It's equivalent to outer_evaluate_let_simple.
def outer_evaluate_arithmetic_simplest : Test :=
(.ok 2, ⟦(let ((x 2)) x)⟧)

def outer_evaluate_arithmetic_let : Test :=
(.ok 20, ⟦(let ((x 2)
                       (y 3)
                       (z 4))
                  (* z (+ x y)))⟧)

def outer_evaluate_arithmetic_comparison : Test :=
(.ok TRUE, ⟦(let ((x 2)
                      (y 3)
                      (z 4))
                 (= 20 (* z
                          (+ x y))))⟧)

def outer_evaluate_fundamental_conditional_1 : Test :=
(.ok 5, ⟦(let ((true (lambda (a)
                              (lambda (b)
                                a)))
                      (false (lambda (a)
                               (lambda (b)
                                 b)))
                      -- NOTE: We cannot shadow IF because it is built_in.
                      (if- (lambda (a)
                             (lambda (c)
                               (lambda (cond)
                                 ((cond a) c))))))
                 (((if- 5) 6) true))⟧)

def outer_evaluate_fundamental_conditional_2 : Test :=
(.ok 6, ⟦(let ((true (lambda (a)
                              (lambda (b)
                                a)))
                      (false (lambda (a)
                               (lambda (b)
                                 b)))
                      -- NOTE: We cannot shadow IF because it is built_in.
                      (if- (lambda (a)
                             (lambda (c)
                               (lambda (cond)
                                 ((cond a) c))))))
                 (((if- 5) 6) false))⟧)

def outer_evaluate_fundamental_conditional_bug : Test :=
(.ok 5, ⟦(let ((true (lambda (a)
                              (lambda (b)
                                a)))
                      -- NOTE: We cannot shadow IF because it is built_in.
                      (if- (lambda (a)
                             (lambda (c)
                               (lambda (cond)
                                 ((cond a) c))))))
                 (((if- 5) 6) true))⟧)

def outer_evaluate_if : Test :=
(.ok 6, ⟦(if nil 5 6)⟧)

def outer_evaluate_fully_evaluates : Test :=
(.ok 10, ⟦(if t (+ 5 5) 6)⟧)

def outer_evaluate_recursion : Test :=
(.ok 125, ⟦(letrec ((exp (lambda (base)
                                  (lambda (exponent)
                                    (if (= 0 exponent)
                                        1
                                        (* base ((exp base) (- exponent 1))))))))
                          ((exp 5) 3))⟧)

def outer_evaluate_recursion_multiarg : Test :=
(.ok 125, ⟦(letrec ((exp (lambda (base exponent)
                                  (if (= 0 exponent)
                                      1
                                      (* base (exp base (- exponent 1)))))))
                          (exp 5 3))⟧)

def outer_evaluate_recursion_optimized : Test :=
(.ok 125, ⟦(let ((exp (lambda (base)
                               (letrec ((base_inner
                                          (lambda (exponent)
                                            (if (= 0 exponent)
                                                1
                                                (* base (base_inner (- exponent 1)))))))
                                        base_inner))))
                   ((exp 5) 3))⟧)

def outer_evaluate_tail_recursion : Test :=
(.ok 125, ⟦(letrec ((exp (lambda (base)
                                  (lambda (exponent_remaining)
                                    (lambda (acc)
                                      (if (= 0 exponent_remaining)
                                          acc
                                          (((exp base) (- exponent_remaining 1)) (* acc base))))))))
                          (((exp 5) 3) 1))⟧)

def outer_evaluate_tail_recursion_somewhat_optimized : Test :=
(.ok 125, ⟦(letrec ((exp (lambda (base)
                                  (letrec ((base_inner
                                             (lambda (exponent_remaining)
                                               (lambda (acc)
                                                 (if (= 0 exponent_remaining)
                                                     acc
                                                     ((base_inner (- exponent_remaining 1)) (* acc base)))))))
                                           base_inner))))
                          (((exp 5) 3) 1))⟧)

def outer_evaluate_no_mutual_recursion : Test :=
(.ok TRUE, ⟦(letrec ((even (lambda (n)
                                 (if (= 0 n)
                                     t
                                     (odd (- n 1)))))
                         (odd (lambda (n)
                                (even (- n 1)))))
                        -- NOTE: This is not true mutual_recursion.
                        -- However, it exercises the behavior of LETREC.
                        (odd 1))⟧)

def outer_evaluate_no_mutual_recursion_err : Test :=
(.error "", ⟦(letrec ((even (lambda (n)
                                  (if (= 0 n)
                                      t
                                      (odd (- n 1)))))
                          (odd (lambda (n)
                                 (even (- n 1)))))
                         -- NOTE: This is not true mutual_recursion.
                         -- However, it exercises the behavior of LETREC.
                         (odd 2))⟧)

def outer_evaluate_let_scope : Test :=
(.error "", ⟦(let ((closure (lambda (x)
                                 -- This use of CLOSURE is unbound.
                                 closure)))
                  (closure 1))⟧)

def outer_evaluate_let_no_body : Test :=
(.error "", ⟦(let ((a 9)))⟧)

def outer_prove_quote_end_is_nil_error : Test :=
(.error "",  (quote (1) (2)))

def outer_prove_if_end_is_nil_error : Test :=
(.error "", ⟦(if nil 5 6 7)⟧)

def outer_prove_binop_rest_is_nil : Test :=
(.error "", ⟦(- 9 8 7)⟧)

def outer_prove_relop_rest_is_nil : Test :=
(.error "", ⟦(= 9 8 7)⟧)

def outer_prove_error_div_by_zero : Test :=
(.error "",  (/ 21 0))

def outer_prove_error_invalid_type_and_not_cons : Test :=
(.error "",  (/ 21 nil))

def outer_prove_evaluate_current_env_rest_is_nil_error : Test :=
(.error "", ⟦(current_env a)⟧)

def outer_prove_evaluate_let_end_is_nil_error : Test :=
(.error "", ⟦(let ((a 1 2)) a)⟧)

def outer_prove_evaluate_letrec_end_is_nil_error : Test :=
(.error "", ⟦(letrec ((a 1 2)) a)⟧)

def outer_prove_evaluate_let_empty_error : Test :=
(.error "", ⟦(let)⟧)

def outer_prove_evaluate_let_empty_body_error : Test :=
(.error "", ⟦(let ((a 1)))⟧)

def outer_prove_evaluate_letrec_empty_error : Test :=
(.error "", ⟦(letrec)⟧)

def outer_prove_evaluate_letrec_empty_body_error : Test :=
(.error "", ⟦(letrec ((a 1)))⟧)

def outer_prove_evaluate_let_rest_body_is_nil_error : Test :=
(.error "", ⟦(let ((a 1)) a 1)⟧)

def outer_prove_evaluate_letrec_rest_body_is_nil_error : Test :=
(.error "", ⟦(letrec ((a 1)) a 1)⟧)

def outer_prove_error_car_end_is_nil_error : Test :=
(.error "", ⟦(car (1 2) 3)⟧)

def outer_prove_error_cdr_end_is_nil_error : Test :=
(.error "", ⟦(cdr (1 2) 3)⟧)

def outer_prove_error_atom_end_is_nil_error : Test :=
(.error "", ⟦(atom 123 4)⟧)

def outer_prove_error_emit_end_is_nil_error : Test :=
(.error "", ⟦(emit 123 4)⟧)

def outer_prove_error_zero_arg_lambda4 : Test :=
(.error "", ⟦((lambda () 123) 1)⟧)

def outer_prove_error_zero_arg_lambda5 : Test :=
(.error "", ⟦(123)⟧)

def outer_evaluate_cons_1 : Test :=
(.ok 1, ⟦(car (cons 1 2))⟧)

def outer_evaluate_cons_2 : Test :=
(.ok 2, ⟦(cdr (cons 1 2))⟧)

def outer_evaluate_cons_in_function_1 : Test :=
(.ok 2, ⟦(((lambda (a)
                   (lambda (b)
                     (car (cons a b))))
                 2)
                3)⟧)

def outer_evaluate_cons_in_function_2 : Test :=
(.ok 3, ⟦(((lambda (a)
                   (lambda (b)
                     (cdr (cons a b))))
                 2)
                3)⟧)

def multiarg_eval_bug : Test :=
(.ok 2, ⟦(car (cdr ,(1 2 3 4)))⟧)

def outer_evaluate_zero_arg_lambda_1 : Test :=
(.ok 123, ⟦((lambda () 123))⟧)

def outer_evaluate_zero_arg_lambda_2 : Test :=
(.ok 10, ⟦(let ((x 9) (f (lambda () (+ x 1)))) (f))⟧)

def minimal_tail_call : Test :=
(.ok 123, ⟦(letrec
                  ((f (lambda (x)
                        (if (= x 140)
                            123
                            (f (+ x 1))))))
                  (f 0))⟧)

def multiple_letrec_bindings : Test :=
(.ok 123, ⟦(letrec
                  ((x 888)
                   (f (lambda (x)
                        (if (= x 5)
                            123
                            (f (+ x 1))))))
                  (f 0))⟧)

def tail_call2 : Test :=
(.ok 123, ⟦(letrec
                  ((f (lambda (x)
                        (if (= x 5)
                            123
                            (f (+ x 1)))))
                   (g (lambda (x) (f x))))
                  (g 0))⟧)

-- def outer_evaluate_make_tree : Test :=
-- (.ok '(((h . g) . (f . e)) . ((d . c) . (b . a)))
--              (letrec ((mapcar (lambda (f list)
--                                  (if (eq list nil)
--                                      nil
--                                      (cons (f (car list)) (mapcar f (cdr list))))))
--                        (make_row (lambda (list)
--                                    (if (eq list nil)
--                                        nil
--                                        (let ((cdr (cdr list)))
--                                          (cons (cons (car list) (car cdr))
--                                                (make_row (cdr cdr)))))))
--                        (make_tree_aux (lambda (list)
--                                         (let ((row (make_row list)))
--                                           (if (eq (cdr row) nil)
--                                               row
--                                               (make_tree_aux row)))))
--                        (make_tree (lambda (list)
--                                     (car (make_tree_aux list))))
--                        (reverse_tree (lambda (tree)
--                                        (if (atom tree)
--                                            tree
--                                            (cons (reverse_tree (cdr tree))
--                                                  (reverse_tree (car tree)))))))
--                       (reverse_tree
--                        (make_tree '(a b c d e f g h)))))

def outer_evaluate_multiple_letrecstar_bindings : Test :=
(.ok 13, ⟦(letrec ((double (lambda (x) (* 2 x)))
                          (square (lambda (x) (* x x))))
                         (+ (square 3) (double 2)))⟧)

-- def outer_evaluate_multiple_letrecstar_bindings_referencing
-- (.ok 11 (letrec ((double (lambda (x) (* 2 x)))
--                           (double_inc (lambda (x) (+ 1 (double x)))))
--                          (+ (double 3) (double_inc 2))))

-- def outer_evaluate_multiple_letrecstar_bindings_recursive
-- (.ok 33 (letrec ((exp (lambda (base exponent)
--                                  (if (= 0 exponent)
--                                      1
--                                      (* base (exp base (_ exponent 1))))))
--                           (exp2 (lambda (base exponent)
--                                   (if (= 0 exponent)
--                                       1
--                                       (* base (exp2 base (_ exponent 1))))))
--                           (exp3 (lambda (base exponent)
--                                   (if (= 0 exponent)
--                                       1
--                                       (* base (exp3 base (_ exponent 1)))))))
--                          (+ (+ (exp 3 2) (exp2 2 3))
--                             (exp3 4 2))))

-- -- dont_discard_rest_env
-- (.ok 18 (let ((z 9))
--                   (letrec ((a 1)
--                             (b 2)
--                             (l (lambda (x) (+ z x))))
--                            (l 9))))

-- -- let_restore_saved_env
-- (.error _,  (+ (let ((a 1)) a) a))

-- -- let_restore_saved_env2
-- (.error _,  (+ (let ((a 1) (a 2)) a) a))

-- -- letrec_restore_saved_env
-- (.error _,  (+ (letrec ((a 1)(a 2)) a) a))

-- -- lookup_restore_saved_env
-- (.error _,  (+ (let ((a 1))
--                      a)
--                    a))

-- -- tail_call_restore_saved_env
-- (.error _,  (let ((outer (letrec
--                                ((x 888)
--                                 (f (lambda (x)
--                                      (if (= x 2)
--                                          123
--                                          (f (+ x 1))))))
--                                f)))
--                   -- This should be an error. X should not be bound here.
--                   (+ (outer 0) x)))

-- -- binop_restore_saved_env
-- (.error _,  (let ((outer (let ((f (lambda (x)
--                                           (+ (let ((a 9)) a) x))))
--                                 f)))
--                   -- This should be an error. X should not be bound here.
--                   (+ (outer 1) x)))

-- -- env_let
-- (.ok '((a . 1)) (let ((a 1)) (current_env)))

-- -- env_let_nested
-- (.ok '((b . 2) (a . 1)) (let ((a 1)) (let ((b 2)) (current_env))))

-- -- env_letrec
-- (.ok '(((a . 1))) (letrec ((a 1)) (current_env)))

-- -- env_letrec_nested
-- (.ok '(((b . 2)  (a . 1))) (letrec ((a 1)) (letrec ((b 2)) (current_env))))

-- -- env_let_letrec_let
-- (.ok '((e . 5) ((d . 4) (c . 3)) (b . 2) (a . 1))
--              (let ((a 1) (b 2)) (letrec ((c 3) (d 4)) (let ((e 5)) (current_env)))))


-- (.ok 3 (begin (emit 1) (emit 2) (emit 3)))

-- (.ok nil (begin))

-- (.ok '((a . 1)) (let ((a 1))
--                           (begin
--                            (let ((b 2))
--                              (emit b))
--                            (current_env))))

-- !(:assert_emitted '(1 2 3) (begin (emit 1) (emit 2) (emit 3)))

-- --; Strings are proper lists of characters and are tagged as such.

-- -- Get the first character of a string with CAR
-- (.ok #\a (car "asdf"))

-- -- Get the tail with CDR
-- (.ok "sdf" (cdr "asdf"))

-- -- Construct a string from a character and another string.
-- (.ok "dog" (strcons #\d "og"))

-- -- Including the empty string.
-- (.ok "z" (strcons #\z ""))

-- -- Construct a pair from a character and another string.
-- (.ok '(#\d . "og") (cons #\d "og"))

-- -- Including the empty string.
-- (.ok '(#\z . "") (cons #\z ""))

-- -- The empty string is the string terminator ("")
-- (.ok "" (cdr "x"))

-- -- The CDR of the empty string is the empty string.
-- (.ok "" (cdr ""))

-- -- The CAR of the empty string is NIL (neither a character nor a string).
-- (.ok nil (car ""))

-- -- CONSing two strings yields a pair, not a string.
-- (.ok '("a" . "b") (cons "a" "b"))

-- -- CONSing two characters yields a pair, not a string.
-- (.ok '(#\a . #\b) (cons #\a #\b))

-- -- STRCONSing two strings is an error.
-- (.error _,  (strcons "a" "b"))

-- -- STRCONSing two characters is an error.
-- (.error _,  (strcons #\a #\b))

-- -- STRCONSing anything but a character and a string is an error.
-- (.error _,  (strcons 1 'foo))

-- --; A char is any 32_bit unicode character, but we currently only have reader support for whatever can be entered directly.
-- (.ok #\Ŵ (car "ŴTF?"))