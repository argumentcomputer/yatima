/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude -- Don't import Init, because we're in Init itself
set_option linter.all false -- prevent error messages from runFrontend

/-!
# Init.Prelude

This is the first file in the lean import hierarchy. It is responsible for setting
up basic definitions, most of which lean already has "built in knowledge" about,
so it is important that they be set up in exactly this way. (For example, lean will
use `PUnit` in the desugaring of `do` notation, or in the pattern match compiler.)

-/

universe u v w

/--
The identity function. `id` takes an implicit argument `α : Sort u`
(a type in any universe), and an argument `a : α`, and returns `a`.

Although this may look like a useless function, one application of the identity
function is to explicitly put a type on an expression. If `e` has type `T`,
and `T'` is definitionally equal to `T`, then `@id T' e` typechecks, and lean
knows that this expression has type `T'` rather than `T`. This can make a
difference for typeclass inference, since `T` and `T'` may have different
typeclass instances on them. `show T' from e` is sugar for an `@id T' e`
expression.
-/
@[inline] def id {α : Sort u} (a : α) : α := a

/--
Function composition is the act of pipelining the result of one function, to the input of another, creating an entirely new function.
Example:
```
#eval Function.comp List.reverse (List.drop 2) [3, 2, 4, 1]
-- [1, 4]
```
You can use the notation `f ∘ g` as shorthand for `Function.comp f g`.
```
#eval (List.reverse ∘ List.drop 2) [3, 2, 4, 1]
-- [1, 4]
```
A simpler way of thinking about it, is that `List.reverse ∘ List.drop 2`
is equivalent to `fun xs => List.reverse (List.drop 2 xs)`,
the benefit is that the meaning of composition is obvious,
and the representation is compact.
-/
@[inline] def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

/--
The constant function. If `a : α`, then `Function.const β a : β → α` is the
"constant function with value `a`", that is, `Function.const β a b = a`.
```
example (b : Bool) : Function.const Bool 10 b = 10 :=
  rfl

#check Function.const Bool 10
-- Bool → Nat
```
-/
@[inline] def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α :=
  fun _ => a

set_option checkBinderAnnotations false in
/--
`inferInstance` synthesizes a value of any target type by typeclass
inference. This function has the same type signature as the identity
function, but the square brackets on the `[i : α]` argument means that it will
attempt to construct this argument by typeclass inference. (This will fail if
`α` is not a `class`.) Example:
```
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

example : foo.default = (default, default) :=
  rfl
```
-/
abbrev inferInstance {α : Sort u} [i : α] : α := i

set_option checkBinderAnnotations false in
/-- `inferInstanceAs α` synthesizes a value of any target type by typeclass
inference. This is just like `inferInstance` except that `α` is given
explicitly instead of being inferred from the target type. It is especially
useful when the target type is some `α'` which is definitionally equal to `α`,
but the instance we are looking for is only registered for `α` (because
typeclass search does not unfold most definitions, but definitional equality
does.) Example:
```
#check inferInstanceAs (Inhabited Nat) -- Inhabited Nat
```
-/
abbrev inferInstanceAs (α : Sort u) [i : α] : α := i

set_option bootstrap.inductiveCheckResultingUniverse false in
/--
The unit type, the canonical type with one element, named `unit` or `()`.
This is the universe-polymorphic version of `Unit`; it is preferred to use
`Unit` instead where applicable.
For more information about universe levels: [Types as objects](https://leanprover.github.io/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects)
-/
inductive PUnit : Sort u where
  /-- `PUnit.unit : PUnit` is the canonical element of the unit type. -/
  | unit : PUnit

/--
The unit type, the canonical type with one element, named `unit` or `()`.
In other words, it describes only a single value, which consists of said constructor applied
to no arguments whatsoever.
The `Unit` type is similar to `void` in languages derived from C.

`Unit` is actually defined as `PUnit.{0}` where `PUnit` is the universe
polymorphic version. The `Unit` should be preferred over `PUnit` where possible to avoid
unnecessary universe parameters.

In functional programming, `Unit` is the return type of things that "return
nothing", since a type with one element conveys no additional information.
When programming with monads, the type `m Unit` represents an action that has
some side effects but does not return a value, while `m α` would be an action
that has side effects and returns a value of type `α`.
-/
abbrev Unit : Type := PUnit

/--
`Unit.unit : Unit` is the canonical element of the unit type.
It can also be written as `()`.
-/
@[match_pattern] abbrev Unit.unit : Unit := PUnit.unit

/-- Marker for information that has been erased by the code generator. -/
unsafe axiom lcErased : Type

/--
Auxiliary unsafe constant used by the Compiler when erasing proofs from code.

It may look strange to have an axiom that says "every proposition is true",
since this is obviously unsound, but the `unsafe` marker ensures that the
kernel will not let this through into regular proofs. The lower levels of the
code generator don't need proofs in terms, so this is used to stub the proofs
out.
-/
unsafe axiom lcProof {α : Prop} : α

/--
Auxiliary unsafe constant used by the Compiler when erasing casts.
-/
unsafe axiom lcCast {α : Sort u} {β : Sort v} (a : α) : β


/--
Auxiliary unsafe constant used by the Compiler to mark unreachable code.

Like `lcProof`, this is an `unsafe axiom`, which means that even though it is
not sound, the kernel will not let us use it for regular proofs.

Executing this expression to actually synthesize a value of type `α` causes
**immediate undefined behavior**, and the compiler does take advantage of this
to optimize the code assuming that it is not called. If it is not optimized out,
it is likely to appear as a print message saying "unreachable code", but this
behavior is not guaranteed or stable in any way.
-/
unsafe axiom lcUnreachable {α : Sort u} : α

/--
`True` is a proposition and has only an introduction rule, `True.intro : True`.
In other words, `True` is simply true, and has a canonical proof, `True.intro`
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
inductive True : Prop where
  /-- `True` is true, and `True.intro` (or more commonly, `trivial`)
  is the proof. -/
  | intro : True

/--
`False` is the empty proposition. Thus, it has no introduction rules.
It represents a contradiction. `False` elimination rule, `False.rec`,
expresses the fact that anything follows from a contradiction.
This rule is sometimes called ex falso (short for ex falso sequitur quodlibet),
or the principle of explosion.
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
inductive False : Prop

/--
The empty type. It has no constructors. The `Empty.rec`
eliminator expresses the fact that anything follows from the empty type.
-/
inductive Empty : Type

set_option bootstrap.inductiveCheckResultingUniverse false in
/--
The universe-polymorphic empty type. Prefer `Empty` or `False` where
possible.
-/
inductive PEmpty : Sort u where

/--
`Not p`, or `¬p`, is the negation of `p`. It is defined to be `p → False`,
so if your goal is `¬p` you can use `intro h` to turn the goal into
`h : p ⊢ False`, and if you have `hn : ¬p` and `h : p` then `hn h : False`
and `(hn h).elim` will prove anything.
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
def Not (a : Prop) : Prop := a → False

/--
`False.elim : False → C` says that from `False`, any desired proposition
`C` holds. Also known as ex falso quodlibet (EFQ) or the principle of explosion.

The target type is actually `C : Sort u` which means it works for both
propositions and types. When executed, this acts like an "unreachable"
instruction: it is **undefined behavior** to run, but it will probably print
"unreachable code". (You would need to construct a proof of false to run it
anyway, which you can only do using `sorry` or unsound axioms.)
-/
@[macro_inline] def False.elim {C : Sort u} (h : False) : C :=
  h.rec

/--
Anything follows from two contradictory hypotheses. Example:
```
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```
For more information: [Propositional Logic](https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)
-/
@[macro_inline] def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
  (h₂ h₁).rec

/--
The equality relation. It has one introduction rule, `Eq.refl`.
We use `a = b` as notation for `Eq a b`.
A fundamental property of equality is that it is an equivalence relation.
```
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```
Equality is much more than an equivalence relation, however. It has the important property that every assertion
respects the equivalence, in the sense that we can substitute equal expressions without changing the truth value.
That is, given `h1 : a = b` and `h2 : p a`, we can construct a proof for `p b` using substitution: `Eq.subst h1 h2`.
Example:
```
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```
The triangle in the second presentation is a macro built on top of `Eq.subst` and `Eq.symm`, and you can enter it by typing `\t`.
For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
inductive Eq : α → α → Prop where
  /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
  equality type. See also `rfl`, which is usually used instead. -/
  | refl (a : α) : Eq a a

/-- Non-dependent recursor for the equality type. -/
@[simp] abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

/--
`rfl : a = a` is the unique constructor of the equality type. This is the
same as `Eq.refl` except that it takes `a` implicitly instead of explicitly.

This is a more powerful theorem than it may appear at first, because although
the statement of the theorem is `a = a`, lean will allow anything that is
definitionally equal to that type. So, for instance, `2 + 2 = 4` is proven in
lean by `rfl`, because both sides are the same up to definitional equality.
-/
@[match_pattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

/-- `id x = x`, as a `@[simp]` lemma. -/
@[simp] theorem id_eq (a : α) : Eq (id a) a := rfl

/--
The substitution principle for equality. If `a = b ` and `P a` holds,
then `P b` also holds. We conventionally use the name `motive` for `P` here,
so that you can specify it explicitly using e.g.
`Eq.subst (motive := fun x => x < 5)` if it is not otherwise inferred correctly.

This theorem is the underlying mechanism behind the `rw` tactic, which is
essentially a fancy algorithm for finding good `motive` arguments to usefully
apply this theorem to replace occurrences of `a` with `b` in the goal or
hypotheses.

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

/--
Equality is symmetric: if `a = b` then `b = a`.

Because this is in the `Eq` namespace, if you have a variable `h : a = b`,
`h.symm` can be used as shorthand for `Eq.symm h` as a proof of `b = a`.

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h ▸ rfl

/--
Equality is transitive: if `a = b` and `b = c` then `a = c`.

Because this is in the `Eq` namespace, if you variables or expressions
`h₁ : a = b` and `h₂ : b = c`, you can use `h₁.trans h₂ : a = c` as shorthand
for `Eq.trans h₁ h₂`.

For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  h₂ ▸ h₁