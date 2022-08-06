def one := Nat.succ Nat.zero
def two := Nat.succ $ Nat.succ $ Nat.zero

def pair := (one, two)

def anotherTwo := pair.2

def toZero : Nat → Nat 
  | 0 => Nat.zero
  | n + 1 => toZero n

-- def isZ (n : Nat) : Bool :=
-- match n with
--   | 0 => true
--   | n + 1 => false

-- def four := two + two

-- inductive Vector (A : Type) : (n : Nat) → Type where
--   | nil : Vector A Nat.zero
--   | cons : {n : Nat} → (a : A) → (as : Vector A n) → Vector A n.succ

/- 
# Example: Three
inductive Three where 
  | A : Three
  | B : Three 
  | C : Three

## Translated Lurk Constructors

`Three.A`:
`["Three", 0]`

`Three.B`:
`["Three", 1]`

`Three.C`:
`["Three", 2]`

## Recursor
Three.rec :
  {motive : Three → Sort u} →
  motive Three.A →
  motive Three.B →
  motive Three.C →
  (t : Three) →
  motive t

## Reduction Rules 

Three.rec {P} caseA caseB caseC Three.A = caseA
Three.rec {P} caseA caseB caseC Three.B = caseB
Three.rec {P} caseA caseB caseC Three.C = caseC

## Translated Lurk Recursor

`Three.rec`:
lambda motive caseA caseB caseC three, 
  if three.cidx == 0 
    return caseA 
  else if three.cidx == 1
    return caseB
  else if three.cidx == 2 
    return caseC

-/

/- 
# Nat 

## Reduction Rules 
Nat.rec {P} caseZero caseSucc Nat.zero = caseZero
Nat.rec {P} caseZero caseSucc (Nat.succ n) =
  caseSucc n (Nat.rec {P} caseZero caseSucc n)

## Translated Lurk Constructors

`Nat.zero`:
`["Nat", 0]`

`Nat.succ`:
`lambda n, ["Nat", 1, n]`

### Yatima Compiled Reduction Rules
Nat.zero 0 
λ (motive : Nat.0 -> (Sort)) (zero : motive.0 Nat.zero.2) (succ : Π (a._@._hyg.4 : Nat.2), (motive.2 a._@._hyg.4.0) -> (motive.3 (Nat.succ.6 a._@._hyg.4.1))) 
  => zero.1
Nat.succ 1 
λ (motive : Nat.0 -> (Sort)) (zero : motive.0 Nat.zero.2) (succ : Π (a._@._hyg.4 : Nat.2), (motive.2 a._@._hyg.4.0) -> (motive.3 (Nat.succ.6 a._@._hyg.4.1))) (a._@._hyg.4 : Nat.3) 
  => succ.1 a._@._hyg.4.0 (Nat.rec.7 motive.3 zero.2 succ.1 a._@._hyg.4.0)

## Translated Lurk Recursor
lambda motive caseZero caseSucc n, 
  if n.cidx == 0
    caseZero
  else if n.cidx == 1 
    caseSucc n (Nat.rec motive caseZero caseSucc n.args)

-/

/-
# Vector

inductive Vector (A : Type) : (n : Nat) → Type where
  | nil : Vector A 0
  | cons : {n : Nat} → (a : A) → (as : Vector A n) → Vector A (n+1)

## Translated Lurk Constructors
`Vector.nil`:
`["Vector", 0]`

`Vector.cons`:
`lambda n a as, ["Vector", 1, n, a, as]`

## Reduction Rules

Vector.rec {A} {P} caseNil caseCons {m} (Vector.nil {A}) = caseNil     -- where m must be equal to 0
Vector.rec {A} {P} caseNil caseCons {m} (Vector.cons {A} {n} a as) =   -- where m must be equal n+1
  caseCons {n} a as (Vector.rec {A} {P} caseNil caseCons {n} as)

### Yatima Compiled Reduction Rules

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

## Translated Lurk Recursor
`Vector.rec`:
lambda A motive caseNil caseCons m `v`,
if `v`.cidx == 0 
  caseNil 
else if `v`.cidx == 1
  (n, a, as) ← `v`.args
  caseCons n a as (Vector.rec A motive caseNil caseCons n as)

-/

-- #check Nat