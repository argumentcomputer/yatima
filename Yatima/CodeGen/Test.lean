import Lean
import Lurk.Backend.DSL

open Lean Compiler
open Lurk.Backend DSL

def prog := ⟦
  (LETREC ((getelem (LAMBDA (xs n) (IF (= n 0) (CAR xs) (getelem (CDR xs) (- n 1)))))
         (drop (LAMBDA (n xs) (IF (= n 0) xs (IF xs (drop (- n 1) (CDR xs)) xs))))
         (to_bool (LAMBDA (x) (IF x (QUOTE ("Bool" 1)) (QUOTE ("Bool" 0)))))
         (lneq (LAMBDA (x y) (IF (EQ x y) NIL T)))
         (Nat_mul (LAMBDA (a b) (* a b)))
         (Nat_div (LAMBDA (a b) (NUM (/ (U64 a) (U64 b)))))
         (_private_Lean_Data_HashMap_0_Lean_numBucketsForCapacity
            (LAMBDA (_uniq_1)
               (LET ((dbg (emit ">> numBucketsForCapacity"))
                     (_uniq_2 4)
                     (_uniq_3 (Nat_mul _uniq_1 _uniq_2))
                     (_uniq_4 3)
                     (_uniq_5 (Nat_div _uniq_3 _uniq_4)))
                  _uniq_5)))
         (Nat_decLt (LAMBDA (a b) (to_bool (< a b))))
         (Nat_nextPowerOfTwo_go__redArg
            (LAMBDA (_uniq_1 _uniq_2)
               (LET ((dbg (emit "nextPowerOfTwo_go"))
                     (dbg (emit _uniq_1))
                     (dbg (emit _uniq_2))
                     (_uniq_3 (Nat_decLt _uniq_2 _uniq_1))
                     (_lurk_idx (getelem _uniq_3 1)))
                  (IF (= _lurk_idx 0)
                     _uniq_2
                     (IF (= _lurk_idx 1)
                        (LET ((_uniq_4 2)
                              (_uniq_5 (Nat_mul _uniq_2 _uniq_4))
                              (_uniq_6 (Nat_nextPowerOfTwo_go__redArg _uniq_1 _uniq_5)))
                           _uniq_6)
                        NIL)))))
         (Nat_nextPowerOfTwo
            (LAMBDA (_uniq_1)
               (LET ((dbg (emit ">> nextPowerOfTwo")) (_uniq_2 1) (_uniq_3 (Nat_nextPowerOfTwo_go__redArg _uniq_1 _uniq_2))) _uniq_3)))
         (Lean_AssocList_nil (LAMBDA (α β) (CONS "Lean_AssocList" (CONS 0 (CONS α (CONS β NIL))))))
         (List_nil (LAMBDA (x) NIL))
         (List_cons (LAMBDA (x head tail) (CONS head tail)))
         (List_replicate__redArg
            (LAMBDA (_uniq_1 _uniq_2)
               (IF (= _uniq_1 0)
                  (LET ((_uniq_3 (List_nil "lcErasedType"))) _uniq_3)
                  (IF (lneq _uniq_1 0)
                     (LET ((_uniq_4 (- _uniq_1 0))
                           (_uniq_5 (List_replicate__redArg _uniq_4 _uniq_2))
                           (_uniq_6 (List_cons "lcErasedType" _uniq_2 _uniq_5)))
                        _uniq_6)
                     NIL))))
         (List_replicate
            (LAMBDA (_uniq_1 _uniq_2 _uniq_3)
               (LET ((_uniq_4 (List_replicate__redArg _uniq_2 _uniq_3))) _uniq_4)))
         (Array_mkArray (LAMBDA (α n v) (List_replicate α n v)))
         (Lean_HashMapImp_mk
            (LAMBDA (α β size buckets)
               (CONS "Lean_HashMapImp" (CONS 0 (CONS α (CONS β (CONS size (CONS buckets NIL))))))))
         (Lean_mkHashMapImp__redArg
            (LAMBDA (_uniq_1)
               (LET ((dbg (emit ">> mkHashMapImp"))
                     (_uniq_2 0)
                     (_uniq_3 (_private_Lean_Data_HashMap_0_Lean_numBucketsForCapacity _uniq_1))
                     (dbg (emit "here 0?"))
                     (_uniq_4 (Nat_nextPowerOfTwo _uniq_3))
                     (dbg (emit "here 1?"))
                     (_uniq_5 (Lean_AssocList_nil "lcErasedType" "lcErasedType"))
                     (dbg (emit "here 2?"))
                     (_uniq_6 (Array_mkArray "lcErased" _uniq_4 _uniq_5))
                     (dbg (emit "here 3?"))
                     (_uniq_7 (Lean_HashMapImp_mk "lcErasedType" "lcErasedType" _uniq_2 _uniq_6))
                     (dbg (emit "hi")))
                  _uniq_7)))
         (hmi (LET ((_uniq_1 8) (_uniq_2 (Lean_mkHashMapImp__redArg _uniq_1)) ) (emit "hi")))
         )
   hmi)
⟧