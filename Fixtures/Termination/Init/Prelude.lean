/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude -- Don't import Init, because we're in Init itself
set_option linter.all false -- prevent error messages from runFrontend

universe u v w

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

@[simp] abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

#print Nat.noConfusionType