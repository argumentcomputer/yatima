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
  fun _ => a

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
  h.rec

@[macroInline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
  (h₂ h₁).rec

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

@[simp] abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

@[matchPattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

@[simp] theorem id_eq (a : α) : Eq (id a) a := rfl

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h ▸ rfl

theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  h₂ ▸ h₁

@[macroInline] def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec a

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

@[matchPattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a :=
  HEq.refl a

theorem eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ => rfl)
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

structure And (a b : Prop) : Prop where
  intro :: (left : a) (right : b)

/-- The type of natural numbers. `0`, `1`, `2`, ...-/
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

set_option bootstrap.genMatcherCode false in
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
