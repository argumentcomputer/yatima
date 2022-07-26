prelude

inductive Nat where 
  | zero : Nat 
  | succ : Nat → Nat 

inductive Vector (A : Type) : (n : Nat) → Type where
  | nil : Vector A Nat.zero
  | cons : {n : Nat} → (a : A) → (as : Vector A n) → Vector A n.succ
/- 
```lean
Three.rec :
  {motive : Three → Sort u} →
  motive Three.A →
  motive Three.B →
  motive Three.C →
  (t : Three) →
  motive t
```

Three.rec {P} caseA caseB caseC Three.A = caseA
Three.rec {P} caseA caseB caseC Three.B = caseB
Three.rec {P} caseA caseB caseC Three.C = caseC

`Three.rec`:
lambda motive cA cB cC three, 
if three.cdr.car == 0 
  return cA 
else if three.cdr.car == 1
  return cB
else if three.cdr.car == 2 
  return cC

-/

/- 

Nat.rec {P} caseZero caseSucc Nat.zero = caseZero
Nat.rec {P} caseZero caseSucc (Nat.succ n) =
  caseSucc n (Nat.rec {P} caseZero caseSucc n)

Nat.zero 0 
λ (motive : Nat.0 -> (Sort)) (zero : motive.0 Nat.zero.2) (succ : Π (a._@._hyg.4 : Nat.2), (motive.2 a._@._hyg.4.0) -> (motive.3 (Nat.succ.6 a._@._hyg.4.1))) 
  => zero.1
Nat.succ 1 
λ (motive : Nat.0 -> (Sort)) (zero : motive.0 Nat.zero.2) (succ : Π (a._@._hyg.4 : Nat.2), (motive.2 a._@._hyg.4.0) -> (motive.3 (Nat.succ.6 a._@._hyg.4.1))) (a._@._hyg.4 : Nat.3) 
  => succ.1 a._@._hyg.4.0 (Nat.rec.7 motive.3 zero.2 succ.1 a._@._hyg.4.0)

lambda motive caseZero caseSucc n, 
if n.ctor == 0
  caseZero
else if n.ctor == 1 
  caseSucc n (Nat.rec motive caseZero caseSucc n.data)

-/

/-

inductive Vector (A : Type) : (n : Nat) → Type where
  | nil : Vector A 0
  | cons : {n : Nat} → (a : A) → (as : Vector A n) → Vector A (n+1)

`Vector.nil`:
`["Vector", 0]`

`Vector.cons`:
`lambda n a as, ["Vector", 1, n, a, as]`

Vector.rec {A} {P} caseNil caseCons {m} (Vector.nil {A}) = caseNil     -- where m must be equal to 0
Vector.rec {A} {P} caseNil caseCons {m} (Vector.cons {A} {n} a as) =   -- where m must be equal n+1
  caseCons {n} a as (Vector.rec {A} {P} caseNil caseCons {n} as)

`Vector.rec`:
lambda A motive caseNil caseCons m `v`,
if `v`.ctor == 0 
  caseNil 
else if `v`.ctor == 1
  (n, a, as) ← `v`.args
  caseCons n a as (Vector.rec A motive caseNil caseCons n as)

Vector.nil 0 
λ (A : Sort) 
  (motive : Π (n : Nat), 
  (Vector.2 A.1 n.0) -> (Sort)) 
  (nil : motive.0 Nat.zero (Vector.nil.3 A.1)) 
  (cons : Π {n : Nat} (a : A.3) (as : Vector.5 A.4 n.1), (motive.4 n.2 as.0) -> (motive.5 (Nat.succ n.3) (Vector.cons.9 A.6 n.3 a.2 as.1))) 
  => nil.1 
Vector.cons 3 
λ (A : Sort) 
  (motive : Π (n : Nat), 
  (Vector.2 A.1 n.0) -> (Sort)) 
  (nil : motive.0 Nat.zero (Vector.nil.3 A.1)) 
  (cons : Π {n : Nat} (a : A.3) (as : Vector.5 A.4 n.1), (motive.4 n.2 as.0) -> (motive.5 (Nat.succ n.3) (Vector.cons.9 A.6 n.3 a.2 as.1))) {n : Nat} (a : A.4) (as : Vector.6 A.5 n.1) 
  => cons.3 n.2 a.1 as.0 (Vector.rec.10 A.6 motive.5 nil.4 cons.3 n.2 as.0)

-/

/-
Expected output:

`Nat.zero`:
`[["Nat", 0], <mdata>]`

`Nat.succ`:
`lambda (n m), [["Nat", 1, n, m], <mdata>]`

-/
#check Nat