/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude

universe u v w

@[inline] def id {α : Sort u} (a : α) : α := a

@[inline] def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

@[inline] def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun x => a

set_option checkBinderAnnotations false in
@[reducible] def inferInstance {α : Sort u} [i : α] : α := i
set_option checkBinderAnnotations false in
@[reducible] def inferInstanceAs (α : Sort u) [i : α] : α := i

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

/-- An abbreviation for `PUnit.{0}`, its most common instantiation.
    This Type should be preferred over `PUnit` where possible to avoid
    unnecessary universe parameters. -/
abbrev Unit : Type := PUnit

@[matchPattern] abbrev Unit.unit : Unit := PUnit.unit

/-- Auxiliary unsafe constant used by the Compiler when erasing proofs from code. -/
unsafe axiom lcProof {α : Prop} : α

/-- Auxiliary unsafe constant used by the Compiler to mark unreachable code. -/
unsafe axiom lcUnreachable {α : Sort u} : α

inductive True : Prop where
  | intro : True

inductive False : Prop

inductive Empty : Type

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PEmpty : Sort u where

def Not (a : Prop) : Prop := a → False

@[macroInline] def False.elim {C : Sort u} (h : False) : C :=
  False.rec (fun _ => C) h

@[macroInline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
  False.elim (h₂ h₁)

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

@[simp] abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  Eq.rec (motive := fun α _ => motive α) m h

@[matchPattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

@[simp] theorem id_eq (a : α) : Eq (id a) a := rfl

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h ▸ rfl

theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  h₂ ▸ h₁

@[macroInline] def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  Eq.rec (motive := fun α _ => α) a h

theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl

theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : Eq f₁ f₂) (h₂ : Eq a₁ a₂) : Eq (f₁ a₁) (f₂ a₂) :=
  h₁ ▸ h₂ ▸ rfl

theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) →  β x} (h : Eq f g) (a : α) : Eq (f a) (g a) :=
  h ▸ rfl

/-
Initialize the Quotient Module, which effectively adds the following definitions:

constant Quot {α : Sort u} (r : α → α → Prop) : Sort u

constant Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : Quot r

constant Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → Eq (f a) (f b)) → Quot r → β

constant Quot.ind {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} :
  (∀ a : α, β (Quot.mk r a)) → ∀ q : Quot r, β q
-/

init_quot

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

@[matchPattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a :=
  HEq.refl a

theorem eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun α β a b h₁ =>
      HEq.rec (motive := fun {β} (b : β) (h : HEq a b) => (h₂ : Eq α β) → Eq (cast h₂ a) b)
        (fun (h₂ : Eq α α) => rfl)
        h₁
  this α α a a' h rfl

structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β

attribute [unbox] Prod

/-- Similar to `Prod`, but `α` and `β` can be propositions.
   We use this Type internally to automatically generate the brecOn recursor. -/
structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

/-- Similar to `Prod`, but `α` and `β` are in the same universe. -/
structure MProd (α β : Type u) where
  fst : α
  snd : β

structure And (a b : Prop) : Prop where
  intro :: (left : a) (right : b)

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

theorem Or.intro_left (b : Prop) (h : a) : Or a b :=
  Or.inl h

theorem Or.intro_right (a : Prop) (h : b) : Or a b :=
  Or.inr h

theorem Or.elim {c : Prop} (h : Or a b) (left : a → c) (right : b → c) : c :=
  match h with
  | Or.inl h => left h
  | Or.inr h => right h

inductive Bool : Type where
  | false : Bool
  | true : Bool

export Bool (false true)

/- Remark: Subtype must take a Sort instead of Type because of the axiom strongIndefiniteDescription. -/
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val

/-- Gadget for optional parameter support. -/
@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

/-- Gadget for marking output parameters in type classes. -/
@[reducible] def outParam (α : Sort u) : Sort u := α

/-- Auxiliary Declaration used to implement the notation (a : α) -/
@[reducible] def typedExpr (α : Sort u) (a : α) : α := a

/-- Auxiliary Declaration used to implement the named patterns `x@h:p` -/
@[reducible] def namedPattern {α : Sort u} (x a : α) (h : Eq x a) : α := a

/- Auxiliary axiom used to implement `sorry`. -/
@[extern "lean_sorry", neverExtract]
axiom sorryAx (α : Sort u) (synthetic := true) : α

theorem eq_false_of_ne_true : {b : Bool} → Not (Eq b true) → Eq b false
  | true, h => False.elim (h rfl)
  | false, h => rfl

theorem eq_true_of_ne_false : {b : Bool} → Not (Eq b false) → Eq b true
  | true, h => rfl
  | false, h => False.elim (h rfl)

theorem ne_false_of_eq_true : {b : Bool} → Eq b true → Not (Eq b false)
  | true, _  => fun h => Bool.noConfusion h
  | false, h => Bool.noConfusion h

theorem ne_true_of_eq_false : {b : Bool} → Eq b false → Not (Eq b true)
  | true, h  => Bool.noConfusion h
  | false, _ => fun h => Bool.noConfusion h

class Inhabited (α : Sort u) where
  default : α

export Inhabited (default)

class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α

axiom Classical.choice {α : Sort u} : Nonempty α → α

protected def Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  match h₁ with
  | intro a => h₂ a

instance {α : Sort u} [Inhabited α] : Nonempty α :=
  ⟨default⟩

noncomputable def Classical.ofNonempty {α : Sort u} [Nonempty α] : α :=
  Classical.choice inferInstance

instance (α : Sort u) {β : Sort v} [Nonempty β] : Nonempty (α → β) :=
  Nonempty.intro fun _ => Classical.ofNonempty

instance (α : Sort u) {β : α → Sort v} [(a : α) → Nonempty (β a)] : Nonempty ((a : α) → β a) :=
  Nonempty.intro fun _ => Classical.ofNonempty

instance : Inhabited (Sort u) where
  default := PUnit

instance (α : Sort u) {β : Sort v} [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default

instance (α : Sort u) {β : α → Sort v} [(a : α) → Inhabited (β a)] : Inhabited ((a : α) → β a) where
  default := fun _ => default

deriving instance Inhabited for Bool

/-- Universe lifting operation from Sort to Type -/
structure PLift (α : Sort u) : Type u where
  up :: (down : α)

/- Bijection between α and PLift α -/
theorem PLift.up_down {α : Sort u} : ∀ (b : PLift α), Eq (up (down b)) b
  | up a => rfl

theorem PLift.down_up {α : Sort u} (a : α) : Eq (down (up a)) a :=
  rfl

/- Pointed types -/
def NonemptyType := Subtype fun α : Type u => Nonempty α

abbrev NonemptyType.type (type : NonemptyType.{u}) : Type u :=
  type.val

instance : Inhabited NonemptyType.{u} where
  default := ⟨PUnit.{u+1}, Nonempty.intro ⟨⟩⟩

/-- Universe lifting operation -/
structure ULift.{r, s} (α : Type s) : Type (max s r) where
  up :: (down : α)

/- Bijection between α and ULift.{v} α -/
theorem ULift.up_down {α : Type u} : ∀ (b : ULift.{v} α), Eq (up (down b)) b
  | up a => rfl

theorem ULift.down_up {α : Type u} (a : α) : Eq (down (up.{v} a)) a :=
  rfl

class inductive Decidable (p : Prop) where
  | isFalse (h : Not p) : Decidable p
  | isTrue  (h : p) : Decidable p

@[inlineIfReduce, nospecialize] def Decidable.decide (p : Prop) [h : Decidable p] : Bool :=
  Decidable.casesOn (motive := fun _ => Bool) h (fun _ => false) (fun _ => true)

export Decidable (isTrue isFalse decide)

abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)

abbrev DecidableRel {α : Sort u} (r : α → α → Prop) :=
  (a b : α) → Decidable (r a b)

abbrev DecidableEq (α : Sort u) :=
  (a b : α) → Decidable (Eq a b)

def decEq {α : Sort u} [s : DecidableEq α] (a b : α) : Decidable (Eq a b) :=
  s a b

theorem decide_eq_true : [s : Decidable p] → p → Eq (decide p) true
  | isTrue  _, _   => rfl
  | isFalse h₁, h₂ => absurd h₂ h₁

theorem decide_eq_false : [s : Decidable p] → Not p → Eq (decide p) false
  | isTrue  h₁, h₂ => absurd h₁ h₂
  | isFalse h, _   => rfl

theorem of_decide_eq_true [s : Decidable p] : Eq (decide p) true → p := fun h =>
  match (generalizing := false) s with
  | isTrue  h₁ => h₁
  | isFalse h₁ => absurd h (ne_true_of_eq_false (decide_eq_false h₁))

theorem of_decide_eq_false [s : Decidable p] : Eq (decide p) false → Not p := fun h =>
  match (generalizing := false) s with
  | isTrue  h₁ => absurd h (ne_false_of_eq_true (decide_eq_true h₁))
  | isFalse h₁ => h₁

theorem of_decide_eq_self_eq_true [s : DecidableEq α] (a : α) : Eq (decide (Eq a a)) true :=
  match (generalizing := false) s a a with
  | isTrue  h₁ => rfl
  | isFalse h₁ => absurd rfl h₁

@[inline] instance : DecidableEq Bool :=
  fun a b => match a, b with
   | false, false => isTrue rfl
   | false, true  => isFalse (fun h => Bool.noConfusion h)
   | true, false  => isFalse (fun h => Bool.noConfusion h)
   | true, true   => isTrue rfl

class BEq (α : Type u) where
  beq : α → α → Bool

open BEq (beq)

instance [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[macroInline] def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t

/- if-then-else -/

@[macroInline] def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

@[macroInline] instance {p q} [dp : Decidable p] [dq : Decidable q] : Decidable (And p q) :=
  match dp with
  | isTrue  hp =>
    match dq with
    | isTrue hq  => isTrue ⟨hp, hq⟩
    | isFalse hq => isFalse (fun h => hq (And.right h))
  | isFalse hp =>
    isFalse (fun h => hp (And.left h))

@[macroInline] instance [dp : Decidable p] [dq : Decidable q] : Decidable (Or p q) :=
  match dp with
  | isTrue  hp => isTrue (Or.inl hp)
  | isFalse hp =>
    match dq with
    | isTrue hq  => isTrue (Or.inr hq)
    | isFalse hq =>
      isFalse fun h => match h with
        | Or.inl h => hp h
        | Or.inr h => hq h

instance [dp : Decidable p] : Decidable (Not p) :=
  match dp with
  | isTrue hp  => isFalse (absurd hp)
  | isFalse hp => isTrue hp

/- Boolean operators -/

@[macroInline] def cond {α : Type u} (c : Bool) (x y : α) : α :=
  match c with
  | true  => x
  | false => y

@[macroInline] def or (x y : Bool) : Bool :=
  match x with
  | true  => true
  | false => y

@[macroInline] def and (x y : Bool) : Bool :=
  match x with
  | false => false
  | true  => y

@[inline] def not : Bool → Bool
  | true  => false
  | false => true

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

instance : Inhabited Nat where
  default := Nat.zero

/- For numeric literals notation -/
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[defaultInstance 100] /- low prio -/
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class LE (α : Type u) where le : α → α → Prop
class LT (α : Type u) where lt : α → α → Prop

@[reducible] def GE.ge {α : Type u} [LE α] (a b : α) : Prop := LE.le b a
@[reducible] def GT.gt {α : Type u} [LT α] (a b : α) : Prop := LT.lt b a

@[inline] def max [LT α] [DecidableRel (@LT.lt α _)] (a b : α) : α :=
  ite (LT.lt b a) a b

@[inline] def min [LE α] [DecidableRel (@LE.le α _)] (a b : α) : α :=
  ite (LE.le a b) a b

/-- Transitive chaining of proofs, used e.g. by `calc`. -/
class Trans (r : α → β → Prop) (s : β → γ → Prop) (t : outParam (α → γ → Prop)) where
  trans : r a b → s b c → t a c

export Trans (trans)

instance (r : α → γ → Prop) : Trans Eq r r where
  trans heq h' := heq ▸ h'

instance (r : α → β → Prop) : Trans r Eq r where
  trans h' heq := heq ▸ h'

class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAdd : α → β → γ

class HSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSub : α → β → γ

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class HDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hDiv : α → β → γ

class HMod (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMod : α → β → γ

class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hPow : α → β → γ

class HAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAppend : α → β → γ

class HOrElse (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hOrElse : α → (Unit → β) → γ

class HAndThen (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAndThen : α → (Unit → β) → γ

class HAnd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAnd : α → β → γ

class HXor (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hXor : α → β → γ

class HOr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hOr : α → β → γ

class HShiftLeft (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hShiftLeft : α → β → γ

class HShiftRight (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hShiftRight : α → β → γ

class Add (α : Type u) where
  add : α → α → α

class Sub (α : Type u) where
  sub : α → α → α

class Mul (α : Type u) where
  mul : α → α → α

class Neg (α : Type u) where
  neg : α → α

class Div (α : Type u) where
  div : α → α → α

class Mod (α : Type u) where
  mod : α → α → α

class Pow (α : Type u) (β : Type v) where
  pow : α → β → α

class Append (α : Type u) where
  append : α → α → α

class OrElse (α : Type u) where
  orElse  : α → (Unit → α) → α

class AndThen (α : Type u) where
  andThen : α → (Unit → α) → α

class AndOp (α : Type u) where
  and : α → α → α

class Xor (α : Type u) where
  xor : α → α → α

class OrOp (α : Type u) where
  or : α → α → α

class Complement (α : Type u) where
  complement : α → α

  class ShiftLeft (α : Type u) where
  shiftLeft : α → α → α

class ShiftRight (α : Type u) where
  shiftRight : α → α → α

@[defaultInstance]
instance [Add α] : HAdd α α α where
  hAdd a b := Add.add a b

@[defaultInstance]
instance [Sub α] : HSub α α α where
  hSub a b := Sub.sub a b

@[defaultInstance]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

@[defaultInstance]
instance [Div α] : HDiv α α α where
  hDiv a b := Div.div a b

@[defaultInstance]
instance [Mod α] : HMod α α α where
  hMod a b := Mod.mod a b

@[defaultInstance]
instance [Pow α β] : HPow α β α where
  hPow a b := Pow.pow a b

@[defaultInstance]
instance [Append α] : HAppend α α α where
  hAppend a b := Append.append a b

@[defaultInstance]
instance [OrElse α] : HOrElse α α α where
  hOrElse a b := OrElse.orElse a b

@[defaultInstance]
instance [AndThen α] : HAndThen α α α where
  hAndThen a b := AndThen.andThen a b

@[defaultInstance]
instance [AndOp α] : HAnd α α α where
  hAnd a b := AndOp.and a b

@[defaultInstance]
instance [Xor α] : HXor α α α where
  hXor a b := Xor.xor a b

@[defaultInstance]
instance [OrOp α] : HOr α α α where
  hOr a b := OrOp.or a b

@[defaultInstance]
instance [ShiftLeft α] : HShiftLeft α α α where
  hShiftLeft a b := ShiftLeft.shiftLeft a b

@[defaultInstance]
instance [ShiftRight α] : HShiftRight α α α where
  hShiftRight a b := ShiftRight.shiftRight a b

open HAdd (hAdd)
open HMul (hMul)
open HPow (hPow)
open HAppend (hAppend)

class Membership (α : outParam (Type u)) (γ : Type v) where
  mem : α → γ → Prop

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

instance : Add Nat where
  add := Nat.add

/- We mark the following definitions as pattern to make sure they can be used in recursive equations,
   and reduced by the equation Compiler. -/
attribute [matchPattern] Nat.add Add.add HAdd.hAdd Neg.neg

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_mul"]
protected def Nat.mul : (@& Nat) → (@& Nat) → Nat
  | a, 0          => 0
  | a, Nat.succ b => Nat.add (Nat.mul a b) a

instance : Mul Nat where
  mul := Nat.mul

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_pow"]
protected def Nat.pow (m : @& Nat) : (@& Nat) → Nat
  | 0      => 1
  | succ n => Nat.mul (Nat.pow m n) m

instance : Pow Nat Nat where
  pow := Nat.pow

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_dec_eq"]
def Nat.beq : (@& Nat) → (@& Nat) → Bool
  | zero,   zero   => true
  | zero,   succ m => false
  | succ n, zero   => false
  | succ n, succ m => beq n m

instance : BEq Nat where
  beq := Nat.beq

theorem Nat.eq_of_beq_eq_true : {n m : Nat} → Eq (beq n m) true → Eq n m
  | zero,   zero,   h => rfl
  | zero,   succ m, h => Bool.noConfusion h
  | succ n, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have : Eq (beq n m) true := h
    have : Eq n m := eq_of_beq_eq_true this
    this ▸ rfl

#print Nat.eq_of_beq_eq_true

theorem Nat.ne_of_beq_eq_false : {n m : Nat} → Eq (beq n m) false → Not (Eq n m)
  | zero,   zero,   h₁, h₂ => Bool.noConfusion h₁
  | zero,   succ m, h₁, h₂ => Nat.noConfusion h₂
  | succ n, zero,   h₁, h₂ => Nat.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have : Eq (beq n m) false := h₁
    Nat.noConfusion h₂ (fun h₂ => absurd h₂ (ne_of_beq_eq_false this))