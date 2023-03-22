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

/--
Cast across a type equality. If `h : α = β` is an equality of types, and
`a : α`, then `a : β` will usually not typecheck directly, but this function
will allow you to work around this and embed `a` in type `β` as `cast h a : β`.
It is best to avoid this function if you can, because it is more complicated
to reason about terms containing casts, but if the types don't match up
definitionally sometimes there isn't anything better you can do.
For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
@[macro_inline] def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec a

/--
Congruence in the function argument: if `a₁ = a₂` then `f a₁ = f a₂` for
any (nondependent) function `f`. This is more powerful than it might look at first, because
you can also use a lambda expression for `f` to prove that
`<something containing a₁> = <something containing a₂>`. This function is used
internally by tactics like `congr` and `simp` to apply equalities inside
subterms.
For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  h ▸ rfl

/--
Congruence in both function and argument. If `f₁ = f₂` and `a₁ = a₂` then
`f₁ a₁ = f₂ a₂`. This only works for nondependent functions; the theorem
statement is more complex in the dependent case.
For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : Eq f₁ f₂) (h₂ : Eq a₁ a₂) : Eq (f₁ a₁) (f₂ a₂) :=
  h₁ ▸ h₂ ▸ rfl

/-- Congruence in the function part of an application: If `f = g` then `f a = g a`. -/
theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : Eq f g) (a : α) : Eq (f a) (g a) :=
  h ▸ rfl

/-!
Initialize the Quotient Module, which effectively adds the following definitions:
```
opaque Quot {α : Sort u} (r : α → α → Prop) : Sort u
opaque Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : Quot r
opaque Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → Eq (f a) (f b)) → Quot r → β
opaque Quot.ind {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} :
  (∀ a : α, β (Quot.mk r a)) → ∀ q : Quot r, β q
```
-/
init_quot

/--
Let `α` be any type, and let `r` be an equivalence relation on `α`.
It is mathematically common to form the "quotient" `α / r`, that is, the type of
elements of `α` "modulo" `r`. Set theoretically, one can view `α / r` as the set
of equivalence classes of `α` modulo `r`. If `f : α → β` is any function that
respects the equivalence relation in the sense that for every `x y : α`,
`r x y` implies `f x = f y`, then f "lifts" to a function `f' : α / r → β`
defined on each equivalence class `⟦x⟧` by `f' ⟦x⟧ = f x`.
Lean extends the Calculus of Constructions with additional constants that
perform exactly these constructions, and installs this last equation as a
definitional reduction rule.
Given a type `α` and any binary relation `r` on `α`, `Quot r` is a type. Note
that `r` is not required to be an equivalance relation. `Quot` is the basic
building block used to construct later the type `Quotient`.
-/
add_decl_doc Quot

/--
Given a type `α` and any binary relation `r` on `α`, `Quot.mk` maps `α` to `Quot r`.
So that if `r : α → α → Prop` and `a : α`, then `Quot.mk r a` is an element of `Quot r`.
See `Quot`.
-/
add_decl_doc Quot.mk

/--
Given a type `α` and any binary relation `r` on `α`,
`Quot.ind` says that every element of `Quot r` is of the form `Quot.mk r a`.
See `Quot` and `Quot.lift`.
-/
add_decl_doc Quot.ind

/--
Given a type `α`, any binary relation `r` on `α`, a function `f : α → β`, and a proof `h`
that `f` respects the relation `r`, then `Quot.lift f h` is the corresponding function on `Quot r`.
The idea is that for each element `a` in `α`, the function `Quot.lift f h` maps `Quot.mk r a`
(the `r`-class containing `a`) to `f a`, wherein `h` shows that this function is well defined.
In fact, the computation principle is declared as a reduction rule.
-/
add_decl_doc Quot.lift

/--
Unsafe auxiliary constant used by the compiler to erase `Quot.lift`.
-/
unsafe axiom Quot.lcInv {α : Sort u} {r : α → α → Prop} (q : Quot r) : α

/--
Heterogeneous equality. `HEq a b` asserts that `a` and `b` have the same
type, and casting `a` across the equality yields `b`, and vice versa.
You should avoid using this type if you can. Heterogeneous equality does not
have all the same properties as `Eq`, because the assumption that the types of
`a` and `b` are equal is often too weak to prove theorems of interest. One
important non-theorem is the analogue of `congr`: If `HEq f g` and `HEq x y`
and `f x` and `g y` are well typed it does not follow that `HEq (f x) (g y)`.
(This does follow if you have `f = g` instead.) However if `a` and `b` have
the same type then `a = b` and `HEq a b` ae equivalent.
-/
inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  /-- Reflexivity of heterogeneous equality. -/
  | refl (a : α) : HEq a a

/-- A version of `HEq.refl` with an implicit argument. -/
@[match_pattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a :=
  HEq.refl a

theorem eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ => rfl)
  this α α a a' h rfl

/--
Product type (aka pair). You can use `α × β` as notation for `Prod α β`.
Given `a : α` and `b : β`, `Prod.mk a b : Prod α β`. You can use `(a, b)`
as notation for `Prod.mk a b`. Moreover, `(a, b, c)` is notation for
`Prod.mk a (Prod.mk b c)`.
Given `p : Prod α β`, `p.1 : α` and `p.2 : β`. They are short for `Prod.fst p`
and `Prod.snd p` respectively. You can also write `p.fst` and `p.snd`.
For more information: [Constructors with Arguments](https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html?highlight=Prod#constructors-with-arguments)
-/
structure Prod (α : Type u) (β : Type v) where
  /-- The first projection out of a pair. if `p : α × β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : α × β` then `p.2 : β`. -/
  snd : β

attribute [unbox] Prod

/--
Similar to `Prod`, but `α` and `β` can be propositions.
We use this Type internally to automatically generate the `brecOn` recursor.
-/
structure PProd (α : Sort u) (β : Sort v) where
  /-- The first projection out of a pair. if `p : PProd α β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : PProd α β` then `p.2 : β`. -/
  snd : β

/--
Similar to `Prod`, but `α` and `β` are in the same universe.
We say `MProd` is the universe monomorphic product type.
-/
structure MProd (α β : Type u) where
  /-- The first projection out of a pair. if `p : MProd α β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : MProd α β` then `p.2 : β`. -/
  snd : β

/--
`And a b`, or `a ∧ b`, is the conjunction of propositions. It can be
constructed and destructed like a pair: if `ha : a` and `hb : b` then
`⟨ha, hb⟩ : a ∧ b`, and if `h : a ∧ b` then `h.left : a` and `h.right : b`.
-/
structure And (a b : Prop) : Prop where
  /-- `And.intro : a → b → a ∧ b` is the constructor for the And operation. -/
  intro ::
  /-- Extract the left conjunct from a conjunction. `h : a ∧ b` then
  `h.left`, also notated as `h.1`, is a proof of `a`. -/
  left : a
  /-- Extract the right conjunct from a conjunction. `h : a ∧ b` then
  `h.right`, also notated as `h.2`, is a proof of `b`. -/
  right : b

/--
`Or a b`, or `a ∨ b`, is the disjunction of propositions. There are two
constructors for `Or`, called `Or.inl : a → a ∨ b` and `Or.inr : b → a ∨ b`,
and you can use `match` or `cases` to destruct an `Or` assumption into the
two cases.
-/
inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b

/-- Alias for `Or.inl`. -/
theorem Or.intro_left (b : Prop) (h : a) : Or a b :=
  Or.inl h

/-- Alias for `Or.inr`. -/
theorem Or.intro_right (a : Prop) (h : b) : Or a b :=
  Or.inr h

/--
Proof by cases on an `Or`. If `a ∨ b`, and both `a` and `b` imply
proposition `c`, then `c` is true.
-/
theorem Or.elim {c : Prop} (h : Or a b) (left : a → c) (right : b → c) : c :=
  match h with
  | Or.inl h => left h
  | Or.inr h => right h

/--
`Bool` is the type of boolean values, `true` and `false`. Classically,
this is equivalent to `Prop` (the type of propositions), but the distinction
is important for programming, because values of type `Prop` are erased in the
code generator, while `Bool` corresponds to the type called `bool` or `boolean`
in most programming languages.
-/
inductive Bool : Type where
  /-- The boolean value `false`, not to be confused with the proposition `False`. -/
  | false : Bool
  /-- The boolean value `true`, not to be confused with the proposition `True`. -/
  | true : Bool

export Bool (false true)

/--
`Subtype p`, usually written as `{x : α // p x}`, is a type which
represents all the elements `x : α` for which `p x` is true. It is structurally
a pair-like type, so if you have `x : α` and `h : p x` then
`⟨x, h⟩ : {x // p x}`. An element `s : {x // p x}` will coerce to `α` but
you can also make it explicit using `s.1` or `s.val`.
-/
structure Subtype {α : Sort u} (p : α → Prop) where
  /-- If `s : {x // p x}` then `s.val : α` is the underlying element in the base
  type. You can also write this as `s.1`, or simply as `s` when the type is
  known from context. -/
  val : α
  /-- If `s : {x // p x}` then `s.2` or `s.property` is the assertion that
  `p s.1`, that is, that `s` is in fact an element for which `p` holds. -/
  property : p val

set_option linter.unusedVariables.funArgs false in
/--
Gadget for optional parameter support.
A binder like `(x : α := default)` in a declaration is syntax sugar for
`x : optParam α default`, and triggers the elaborator to attempt to use
`default` to supply the argument if it is not supplied.
-/
@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

/--
Gadget for marking output parameters in type classes.
For example, the `Membership` class is defined as:
```
class Membership (α : outParam (Type u)) (γ : Type v)
```
This means that whenever a typeclass goal of the form `Membership ?α ?γ` comes
up, lean will wait to solve it until `?γ` is known, but then it will run
typeclass inference, and take the first solution it finds, for any value of `?α`,
which thereby determines what `?α` should be.
This expresses that in a term like `a ∈ s`, `s` might be a `Set α` or
`List α` or some other type with a membership operation, and in each case
the "member" type `α` is determined by looking at the container type.
-/
@[reducible] def outParam (α : Sort u) : Sort u := α

set_option linter.unusedVariables.funArgs false in
/-- Auxiliary declaration used to implement named patterns like `x@h:p`. -/
@[reducible] def namedPattern {α : Sort u} (x a : α) (h : Eq x a) : α := a

/--
Auxiliary axiom used to implement `sorry`.
The `sorry` term/tactic expands to `sorryAx _ (synthetic := false)`. This is a
proof of anything, which is intended for stubbing out incomplete parts of a
proof while still having a syntactically correct proof skeleton. Lean will give
a warning whenever a proof uses `sorry`, so you aren't likely to miss it, but
you can double check if a theorem depends on `sorry` by using
`#print axioms my_thm` and looking for `sorryAx` in the axiom list.
The `synthetic` flag is false when written explicitly by the user, but it is
set to `true` when a tactic fails to prove a goal, or if there is a type error
in the expression. A synthetic `sorry` acts like a regular one, except that it
suppresses follow-up errors in order to prevent one error from causing a cascade
of other errors because the desired term was not constructed.
-/
@[extern "lean_sorry", never_extract]
axiom sorryAx (α : Sort u) (synthetic := false) : α

theorem eq_false_of_ne_true : {b : Bool} → Not (Eq b true) → Eq b false
  | true, h => False.elim (h rfl)
  | false, _ => rfl

theorem eq_true_of_ne_false : {b : Bool} → Not (Eq b false) → Eq b true
  | true, _ => rfl
  | false, h => False.elim (h rfl)

theorem ne_false_of_eq_true : {b : Bool} → Eq b true → Not (Eq b false)
  | true, _  => fun h => Bool.noConfusion h
  | false, h => Bool.noConfusion h

theorem ne_true_of_eq_false : {b : Bool} → Eq b false → Not (Eq b true)
  | true, h  => Bool.noConfusion h
  | false, _ => fun h => Bool.noConfusion h

/--
`Inhabited α` is a typeclass that says that `α` has a designated element,
called `(default : α)`. This is sometimes referred to as a "pointed type".
This class is used by functions that need to return a value of the type
when called "out of domain". For example, `Array.get! arr i : α` returns
a value of type `α` when `arr : Array α`, but if `i` is not in range of
the array, it reports a panic message, but this does not halt the program,
so it must still return a value of type `α` (and in fact this is required
for logical consistency), so in this case it returns `default`.
-/
class Inhabited (α : Sort u) where
  /-- `default` is a function that produces a "default" element of any
  `Inhabited` type. This element does not have any particular specified
  properties, but it is often an all-zeroes value. -/
  default : α

export Inhabited (default)

/--
`Nonempty α` is a typeclass that says that `α` is not an empty type,
that is, there exists an element in the type. It differs from `Inhabited α`
in that `Nonempty α` is a `Prop`, which means that it does not actually carry
an element of `α`, only a proof that *there exists* such an element.
Given `Nonempty α`, you can construct an element of `α` *nonconstructively*
using `Classical.choice`.
-/
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α

/--
**The axiom of choice**. `Nonempty α` is a proof that `α` has an element,
but the element itself is erased. The axiom `choice` supplies a particular
element of `α` given only this proof.
The textbook axiom of choice normally makes a family of choices all at once,
but that is implied from this formulation, because if `α : ι → Type` is a
family of types and `h : ∀ i, Nonempty (α i)` is a proof that they are all
nonempty, then `fun i => Classical.choice (h i) : ∀ i, α i` is a family of
chosen elements. This is actually a bit stronger than the ZFC choice axiom;
this is sometimes called "[global choice](https://en.wikipedia.org/wiki/Axiom_of_global_choice)".
In lean, we use the axiom of choice to derive the law of excluded middle
(see `Classical.em`), so it will often show up in axiom listings where you
may not expect. You can use `#print axioms my_thm` to find out if a given
theorem depends on this or other axioms.
This axiom can be used to construct "data", but obviously there is no algorithm
to compute it, so lean will require you to mark any definition that would
involve executing `Classical.choice` or other axioms as `noncomputable`, and
will not produce any executable code for such definitions.
-/
axiom Classical.choice {α : Sort u} : Nonempty α → α

/--
The elimination principle for `Nonempty α`. If `Nonempty α`, and we can
prove `p` given any element `x : α`, then `p` holds. Note that it is essential
that `p` is a `Prop` here; the version with `p` being a `Sort u` is equivalent
to `Classical.choice`.
-/
protected def Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  match h₁ with
  | intro a => h₂ a

instance {α : Sort u} [Inhabited α] : Nonempty α :=
  ⟨default⟩

/--
A variation on `Classical.choice` that uses typeclass inference to
infer the proof of `Nonempty α`.
-/
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

/-- Universe lifting operation from `Sort u` to `Type u`. -/
structure PLift (α : Sort u) : Type u where
  /-- Lift a value into `PLift α` -/    up ::
  /-- Extract a value from `PLift α` -/ down : α

/-- Bijection between `α` and `PLift α` -/
theorem PLift.up_down {α : Sort u} (b : PLift α) : Eq (up (down b)) b := rfl

/-- Bijection between `α` and `PLift α` -/
theorem PLift.down_up {α : Sort u} (a : α) : Eq (down (up a)) a := rfl

/--
`NonemptyType.{u}` is the type of nonempty types in universe `u`.
It is mainly used in constant declarations where we wish to introduce a type
and simultaneously assert that it is nonempty, but otherwise make the type
opaque.
-/
def NonemptyType := Subtype fun α : Type u => Nonempty α

/-- The underlying type of a `NonemptyType`. -/
abbrev NonemptyType.type (type : NonemptyType.{u}) : Type u :=
  type.val

/-- `NonemptyType` is inhabited, because `PUnit` is a nonempty type. -/
instance : Inhabited NonemptyType.{u} where
  default := ⟨PUnit, ⟨⟨⟩⟩⟩

/--
Universe lifting operation from a lower `Type` universe to a higher one.
To express this using level variables, the input is `Type s` and the output is
`Type (max s r)`, so if `s ≤ r` then the latter is (definitionally) `Type r`.
The universe variable `r` is written first so that `ULift.{r} α` can be used
when `s` can be inferred from the type of `α`.
-/
structure ULift.{r, s} (α : Type s) : Type (max s r) where
  /-- Lift a value into `ULift α` -/    up ::
  /-- Extract a value from `ULift α` -/ down : α

/-- Bijection between `α` and `ULift.{v} α` -/
theorem ULift.up_down {α : Type u} (b : ULift.{v} α) : Eq (up (down b)) b := rfl

/-- Bijection between `α` and `ULift.{v} α` -/
theorem ULift.down_up {α : Type u} (a : α) : Eq (down (up.{v} a)) a := rfl

/--
`Decidable p` is a data-carrying class that supplies a proof that `p` is
either `true` or `false`. It is equivalent to `Bool` (and in fact it has the
same code generation as `Bool`) together with a proof that the `Bool` is
true iff `p` is.
`Decidable` instances are used to infer "computation strategies" for
propositions, so that you can have the convenience of writing propositions
inside `if` statements and executing them (which actually executes the inferred
decidability instance instead of the proposition, which has no code).
If a proposition `p` is `Decidable`, then `(by decide : p)` will prove it by
evaluating the decidability instance to `isTrue h` and returning `h`.
-/
class inductive Decidable (p : Prop) where
  /-- Prove that `p` is decidable by supplying a proof of `¬p` -/
  | isFalse (h : Not p) : Decidable p
  /-- Prove that `p` is decidable by supplying a proof of `p` -/
  | isTrue (h : p) : Decidable p

/--
Convert a decidable proposition into a boolean value.
If `p : Prop` is decidable, then `decide p : Bool` is the boolean value
which is `true` if `p` is true and `false` if `p` is false.
-/
@[inline_if_reduce, nospecialize] def Decidable.decide (p : Prop) [h : Decidable p] : Bool :=
  h.casesOn (fun _ => false) (fun _ => true)

export Decidable (isTrue isFalse decide)

/-- A decidable predicate. See `Decidable`. -/
abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)

/-- A decidable relation. See `Decidable`. -/
abbrev DecidableRel {α : Sort u} (r : α → α → Prop) :=
  (a b : α) → Decidable (r a b)

/--
Asserts that `α` has decidable equality, that is, `a = b` is decidable
for all `a b : α`. See `Decidable`.
-/
abbrev DecidableEq (α : Sort u) :=
  (a b : α) → Decidable (Eq a b)

/-- Proves that `a = b` is decidable given `DecidableEq α`. -/
def decEq {α : Sort u} [inst : DecidableEq α] (a b : α) : Decidable (Eq a b) :=
  inst a b

set_option linter.unusedVariables false in
theorem decide_eq_true : [inst : Decidable p] → p → Eq (decide p) true
  | isTrue  _, _   => rfl
  | isFalse h₁, h₂ => absurd h₂ h₁

theorem decide_eq_false : [Decidable p] → Not p → Eq (decide p) false
  | isTrue  h₁, h₂ => absurd h₁ h₂
  | isFalse _, _   => rfl

theorem of_decide_eq_true [inst : Decidable p] : Eq (decide p) true → p := fun h =>
  match (generalizing := false) inst with
  | isTrue  h₁ => h₁
  | isFalse h₁ => absurd h (ne_true_of_eq_false (decide_eq_false h₁))

theorem of_decide_eq_false [inst : Decidable p] : Eq (decide p) false → Not p := fun h =>
  match (generalizing := false) inst with
  | isTrue  h₁ => absurd h (ne_false_of_eq_true (decide_eq_true h₁))
  | isFalse h₁ => h₁

theorem of_decide_eq_self_eq_true [inst : DecidableEq α] (a : α) : Eq (decide (Eq a a)) true :=
  match (generalizing := false) inst a a with
  | isTrue  _  => rfl
  | isFalse h₁ => absurd rfl h₁

/-- Decidable equality for Bool -/
@[inline] def Bool.decEq (a b : Bool) : Decidable (Eq a b) :=
   match a, b with
   | false, false => isTrue rfl
   | false, true  => isFalse (fun h => Bool.noConfusion h)
   | true, false  => isFalse (fun h => Bool.noConfusion h)
   | true, true   => isTrue rfl

@[inline] instance : DecidableEq Bool :=
   Bool.decEq

/--
`BEq α` is a typeclass for supplying a boolean-valued equality relation on
`α`, notated as `a == b`. Unlike `DecidableEq α` (which uses `a = b`), this
is `Bool` valued instead of `Prop` valued, and it also does not have any
axioms like being reflexive or agreeing with `=`. It is mainly intended for
programming applications. See `LawfulBEq` for a version that requires that
`==` and `=` coincide.
-/
class BEq (α : Type u) where
  /-- Boolean equality, notated as `a == b`. -/
  beq : α → α → Bool

open BEq (beq)

instance [DecidableEq α] : BEq α where
  beq a b := decide (Eq a b)


/--
"Dependent" if-then-else, normally written via the notation `if h : c then t(h) else e(h)`,
is sugar for `dite c (fun h => t(h)) (fun h => e(h))`, and it is the same as
`if c then t else e` except that `t` is allowed to depend on a proof `h : c`,
and `e` can depend on `h : ¬c`. (Both branches use the same name for the hypothesis,
even though it has different types in the two cases.)
We use this to be able to communicate the if-then-else condition to the branches.
For example, `Array.get arr ⟨i, h⟩` expects a proof `h : i < arr.size` in order to
avoid a bounds check, so you can write `if h : i < arr.size then arr.get ⟨i, h⟩ else ...`
to avoid the bounds check inside the if branch. (Of course in this case we have only
lifted the check into an explicit `if`, but we could also use this proof multiple times
or derive `i < arr.size` from some other proposition that we are checking in the `if`.)
-/
@[macro_inline] def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  h.casesOn e t

/-! # if-then-else -/

/--
`if c then t else e` is notation for `ite c t e`, "if-then-else", which decides to
return `t` or `e` depending on whether `c` is true or false. The explicit argument
`c : Prop` does not have any actual computational content, but there is an additional
`[Decidable c]` argument synthesized by typeclass inference which actually
determines how to evaluate `c` to true or false.
Because lean uses a strict (call-by-value) evaluation strategy, the signature of this
function is problematic in that it would require `t` and `e` to be evaluated before
calling the `ite` function, which would cause both sides of the `if` to be evaluated.
Even if the result is discarded, this would be a big performance problem,
and is undesirable for users in any case. To resolve this, `ite` is marked as
`@[macro_inline]`, which means that it is unfolded during code generation, and
the definition of the function uses `fun _ => t` and `fun _ => e` so this recovers
the expected "lazy" behavior of `if`: the `t` and `e` arguments delay evaluation
until `c` is known.
-/
@[macro_inline] def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  h.casesOn (fun _ => e) (fun _ => t)

@[macro_inline] instance {p q} [dp : Decidable p] [dq : Decidable q] : Decidable (And p q) :=
  match dp with
  | isTrue  hp =>
    match dq with
    | isTrue hq  => isTrue ⟨hp, hq⟩
    | isFalse hq => isFalse (fun h => hq (And.right h))
  | isFalse hp =>
    isFalse (fun h => hp (And.left h))

@[macro_inline] instance [dp : Decidable p] [dq : Decidable q] : Decidable (Or p q) :=
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

/-! # Boolean operators -/

/--
`cond b x y` is the same as `if b then x else y`, but optimized for a
boolean condition. It can also be written as `bif b then x else y`.
This is `@[macro_inline]` because `x` and `y` should not
be eagerly evaluated (see `ite`).
-/
@[macro_inline] def cond {α : Type u} (c : Bool) (x y : α) : α :=
  match c with
  | true  => x
  | false => y

/--
`or x y`, or `x || y`, is the boolean "or" operation (not to be confused
with `Or : Prop → Prop → Prop`, which is the propositional connective).
It is `@[macro_inline]` because it has C-like short-circuiting behavior:
if `x` is true then `y` is not evaluated.
-/
@[macro_inline] def or (x y : Bool) : Bool :=
  match x with
  | true  => true
  | false => y

/--
`and x y`, or `x && y`, is the boolean "and" operation (not to be confused
with `And : Prop → Prop → Prop`, which is the propositional connective).
It is `@[macro_inline]` because it has C-like short-circuiting behavior:
if `x` is false then `y` is not evaluated.
-/
@[macro_inline] def and (x y : Bool) : Bool :=
  match x with
  | false => false
  | true  => y

/--
`not x`, or `!x`, is the boolean "not" operation (not to be confused
with `Not : Prop → Prop`, which is the propositional connective).
-/
@[inline] def not : Bool → Bool
  | true  => false
  | false => true

/--
The type of natural numbers, starting at zero. It is defined as an
inductive type freely generated by "zero is a natural number" and
"the successor of a natural number is a natural number".
You can prove a theorem `P n` about `n : Nat` by `induction n`, which will
expect a proof of the theorem for `P 0`, and a proof of `P (succ i)` assuming
a proof of `P i`. The same method also works to define functions by recursion
on natural numbers: induction and recursion are two expressions of the same
operation from lean's point of view.
```
open Nat
example (n : Nat) : n < succ n := by
  induction n with
  | zero =>
    show 0 < 1
    decide
  | succ i ih => -- ih : i < succ i
    show succ i < succ (succ i)
    exact Nat.succ_lt_succ ih
```
This type is special-cased by both the kernel and the compiler:
* The type of expressions contains "`Nat` literals" as a primitive constructor,
  and the kernel knows how to reduce zero/succ expressions to nat literals.
* If implemented naively, this type would represent a numeral `n` in unary as a
  linked list with `n` links, which is horribly inefficient. Instead, the
  runtime itself has a special representation for `Nat` which stores numbers up
  to 2^63 directly and larger numbers use an arbitrary precision "bignum"
  library (usually [GMP](https://gmplib.org/)).
-/
inductive Nat where
  /-- `Nat.zero`, normally written `0 : Nat`, is the smallest natural number.
  This is one of the two constructors of `Nat`. -/
  | zero : Nat
  /-- The successor function on natural numbers, `succ n = n + 1`.
  This is one of the two constructors of `Nat`. -/
  | succ (n : Nat) : Nat

instance : Inhabited Nat where
  default := Nat.zero

/--
The class `OfNat α n` powers the numeric literal parser. If you write
`37 : α`, lean will attempt to synthesize `OfNat α 37`, and will generate
the term `(OfNat.ofNat 37 : α)`.
There is a bit of infinite regress here since the desugaring apparently
still contains a literal `37` in it. The type of expressions contains a
primitive constructor for "raw natural number literals", which you can directly
access using the macro `nat_lit 37`. Raw number literals are always of type `Nat`.
So it would be more correct to say that lean looks for an instance of
`OfNat α (nat_lit 37)`, and it generates the term `(OfNat.ofNat (nat_lit 37) : α)`.
-/
class OfNat (α : Type u) (_ : Nat) where
  /-- The `OfNat.ofNat` function is automatically inserted by the parser when
  the user writes a numeric literal like `1 : α`. Implementations of this
  typeclass can therefore customize the behavior of `n : α` based on `n` and
  `α`. -/
  ofNat : α

@[default_instance 100] /- low prio -/
instance (n : Nat) : OfNat Nat n where
  ofNat := n

/-- `LE α` is the typeclass which supports the notation `x ≤ y` where `x y : α`.-/
class LE (α : Type u) where
  /-- The less-equal relation: `x ≤ y` -/
  le : α → α → Prop

/-- `LT α` is the typeclass which supports the notation `x < y` where `x y : α`.-/
class LT (α : Type u) where
  /-- The less-than relation: `x < y` -/
  lt : α → α → Prop

/-- `a ≥ b` is an abbreviation for `b ≤ a`. -/
@[reducible] def GE.ge {α : Type u} [LE α] (a b : α) : Prop := LE.le b a
/-- `a > b` is an abbreviation for `b < a`. -/
@[reducible] def GT.gt {α : Type u} [LT α] (a b : α) : Prop := LT.lt b a

/-- `Max α` is the typeclass which supports the operation `max x y` where `x y : α`.-/
class Max (α : Type u) where
  /-- The maximum operation: `max x y`. -/
  max : α → α → α

export Max (max)

/-- Implementation of the `max` operation using `≤`. -/
-- Marked inline so that `min x y + max x y` can be optimized to a single branch.
@[inline]
def maxOfLe [LE α] [DecidableRel (@LE.le α _)] : Max α where
  max x y := ite (LE.le x y) y x

/-- `Min α` is the typeclass which supports the operation `min x y` where `x y : α`.-/
class Min (α : Type u) where
  /-- The minimum operation: `min x y`. -/
  min : α → α → α

export Min (min)

/-- Implementation of the `min` operation using `≤`. -/
-- Marked inline so that `min x y + max x y` can be optimized to a single branch.
@[inline]
def minOfLe [LE α] [DecidableRel (@LE.le α _)] : Min α where
  min x y := ite (LE.le x y) x y

/--
Transitive chaining of proofs, used e.g. by `calc`.
It takes two relations `r` and `s` as "input", and produces an "output"
relation `t`, with the property that `r a b` and `s b c` implies `t a c`.
The `calc` tactic uses this so that when it sees a chain with `a ≤ b` and `b < c`
it knows that this should be a proof of `a < c` because there is an instance
`Trans (·≤·) (·<·) (·<·)`.
-/
class Trans (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) where
  /-- Compose two proofs by transitivity, generalized over the relations involved. -/
  trans : r a b → s b c → t a c

export Trans (trans)

instance (r : α → γ → Sort u) : Trans Eq r r where
  trans heq h' := heq ▸ h'

instance (r : α → β → Sort u) : Trans r Eq r where
  trans h' heq := heq ▸ h'

/--
The notation typeclass for heterogeneous addition.
This enables the notation `a + b : γ` where `a : α`, `b : β`.
-/
class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a + b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hAdd : α → β → γ

/--
The notation typeclass for heterogeneous subtraction.
This enables the notation `a - b : γ` where `a : α`, `b : β`.
-/
class HSub (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a - b` computes the difference of `a` and `b`.
  The meaning of this notation is type-dependent.
  * For natural numbers, this operator saturates at 0: `a - b = 0` when `a ≤ b`. -/
  hSub : α → β → γ

/--
The notation typeclass for heterogeneous multiplication.
This enables the notation `a * b : γ` where `a : α`, `b : β`.
-/
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a * b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hMul : α → β → γ

/--
The notation typeclass for heterogeneous division.
This enables the notation `a / b : γ` where `a : α`, `b : β`.
-/
class HDiv (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a / b` computes the result of dividing `a` by `b`.
  The meaning of this notation is type-dependent.
  * For most types like `Nat`, `Int`, `Rat`, `Real`, `a / 0` is defined to be `0`.
  * For `Nat` and `Int`, `a / b` rounds toward 0.
  * For `Float`, `a / 0` follows the IEEE 754 semantics for division,
    usually resulting in `inf` or `nan`. -/
  hDiv : α → β → γ

/--
The notation typeclass for heterogeneous modulo / remainder.
This enables the notation `a % b : γ` where `a : α`, `b : β`.
-/
class HMod (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a % b` computes the remainder upon dividing `a` by `b`.
  The meaning of this notation is type-dependent.
  * For `Nat` and `Int`, `a % 0` is defined to be `a`. -/
  hMod : α → β → γ

/--
The notation typeclass for heterogeneous exponentiation.
This enables the notation `a ^ b : γ` where `a : α`, `b : β`.
-/
class HPow (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ^ b` computes `a` to the power of `b`.
  The meaning of this notation is type-dependent. -/
  hPow : α → β → γ

/--
The notation typeclass for heterogeneous append.
This enables the notation `a ++ b : γ` where `a : α`, `b : β`.
-/
class HAppend (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ++ b` is the result of concatenation of `a` and `b`, usually read "append".
  The meaning of this notation is type-dependent. -/
  hAppend : α → β → γ

/--
The typeclass behind the notation `a <|> b : γ` where `a : α`, `b : β`.
Because `b` is "lazy" in this notation, it is passed as `Unit → β` to the
implementation so it can decide when to evaluate it.
-/
class HOrElse (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a <|> b` executes `a` and returns the result, unless it fails in which
  case it executes and returns `b`. Because `b` is not always executed, it
  is passed as a thunk so it can be forced only when needed.
  The meaning of this notation is type-dependent. -/
  hOrElse : α → (Unit → β) → γ

/--
The typeclass behind the notation `a >> b : γ` where `a : α`, `b : β`.
Because `b` is "lazy" in this notation, it is passed as `Unit → β` to the
implementation so it can decide when to evaluate it.
-/
class HAndThen (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a >> b` executes `a`, ignores the result, and then executes `b`.
  If `a` fails then `b` is not executed. Because `b` is not always executed, it
  is passed as a thunk so it can be forced only when needed.
  The meaning of this notation is type-dependent. -/
  hAndThen : α → (Unit → β) → γ

/-- The typeclass behind the notation `a &&& b : γ` where `a : α`, `b : β`. -/
class HAnd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a &&& b` computes the bitwise AND of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hAnd : α → β → γ

/-- The typeclass behind the notation `a ^^^ b : γ` where `a : α`, `b : β`. -/
class HXor (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ^^^ b` computes the bitwise XOR of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hXor : α → β → γ

/-- The typeclass behind the notation `a ||| b : γ` where `a : α`, `b : β`. -/
class HOr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ||| b` computes the bitwise OR of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hOr : α → β → γ

/-- The typeclass behind the notation `a <<< b : γ` where `a : α`, `b : β`. -/
class HShiftLeft (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a <<< b` computes `a` shifted to the left by `b` places.
  The meaning of this notation is type-dependent.
  * On `Nat`, this is equivalent to `a * 2 ^ b`.
  * On `UInt8` and other fixed width unsigned types, this is the same but
    truncated to the bit width. -/
  hShiftLeft : α → β → γ

/-- The typeclass behind the notation `a >>> b : γ` where `a : α`, `b : β`. -/
class HShiftRight (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a >>> b` computes `a` shifted to the right by `b` places.
  The meaning of this notation is type-dependent.
  * On `Nat` and fixed width unsigned types like `UInt8`,
    this is equivalent to `a / 2 ^ b`. -/
  hShiftRight : α → β → γ

/-- The homogeneous version of `HAdd`: `a + b : α` where `a b : α`. -/
class Add (α : Type u) where
  /-- `a + b` computes the sum of `a` and `b`. See `HAdd`. -/
  add : α → α → α

/-- The homogeneous version of `HSub`: `a - b : α` where `a b : α`. -/
class Sub (α : Type u) where
  /-- `a - b` computes the difference of `a` and `b`. See `HSub`. -/
  sub : α → α → α

/-- The homogeneous version of `HMul`: `a * b : α` where `a b : α`. -/
class Mul (α : Type u) where
  /-- `a * b` computes the product of `a` and `b`. See `HMul`. -/
  mul : α → α → α

/--
The notation typeclass for negation.
This enables the notation `-a : α` where `a : α`.
-/
class Neg (α : Type u) where
  /-- `-a` computes the negative or opposite of `a`.
  The meaning of this notation is type-dependent. -/
  neg : α → α

/-- The homogeneous version of `HDiv`: `a / b : α` where `a b : α`. -/
class Div (α : Type u) where
  /-- `a / b` computes the result of dividing `a` by `b`. See `HDiv`. -/
  div : α → α → α

/-- The homogeneous version of `HMod`: `a % b : α` where `a b : α`. -/
class Mod (α : Type u) where
  /-- `a % b` computes the remainder upon dividing `a` by `b`. See `HMod`. -/
  mod : α → α → α

/--
The homogeneous version of `HPow`: `a ^ b : α` where `a : α`, `b : β`.
(The right argument is not the same as the left since we often want this even
in the homogeneous case.)
-/
class Pow (α : Type u) (β : Type v) where
  /-- `a ^ b` computes `a` to the power of `b`. See `HPow`. -/
  pow : α → β → α

/-- The homogeneous version of `HAppend`: `a ++ b : α` where `a b : α`. -/
class Append (α : Type u) where
  /-- `a ++ b` is the result of concatenation of `a` and `b`. See `HAppend`. -/
  append : α → α → α

/--
The homogeneous version of `HOrElse`: `a <|> b : α` where `a b : α`.
Because `b` is "lazy" in this notation, it is passed as `Unit → α` to the
implementation so it can decide when to evaluate it.
-/
class OrElse (α : Type u) where
  /-- The implementation of `a <|> b : α`. See `HOrElse`. -/
  orElse  : α → (Unit → α) → α

/--
The homogeneous version of `HAndThen`: `a >> b : α` where `a b : α`.
Because `b` is "lazy" in this notation, it is passed as `Unit → α` to the
implementation so it can decide when to evaluate it.
-/
class AndThen (α : Type u) where
  /-- The implementation of `a >> b : α`. See `HAndThen`. -/
  andThen : α → (Unit → α) → α

/--
The homogeneous version of `HAnd`: `a &&& b : α` where `a b : α`.
(It is called `AndOp` because `And` is taken for the propositional connective.)
-/
class AndOp (α : Type u) where
  /-- The implementation of `a &&& b : α`. See `HAnd`. -/
  and : α → α → α

/-- The homogeneous version of `HXor`: `a ^^^ b : α` where `a b : α`. -/
class Xor (α : Type u) where
  /-- The implementation of `a ^^^ b : α`. See `HXor`. -/
  xor : α → α → α

/--
The homogeneous version of `HOr`: `a ||| b : α` where `a b : α`.
(It is called `OrOp` because `Or` is taken for the propositional connective.)
-/
class OrOp (α : Type u) where
  /-- The implementation of `a ||| b : α`. See `HOr`. -/
  or : α → α → α

/-- The typeclass behind the notation `~~~a : α` where `a : α`. -/
class Complement (α : Type u) where
  /-- The implementation of `~~~a : α`. -/
  complement : α → α

/-- The homogeneous version of `HShiftLeft`: `a <<< b : α` where `a b : α`. -/
class ShiftLeft (α : Type u) where
  /-- The implementation of `a <<< b : α`. See `HShiftLeft`. -/
  shiftLeft : α → α → α

/-- The homogeneous version of `HShiftRight`: `a >>> b : α` where `a b : α`. -/
class ShiftRight (α : Type u) where
  /-- The implementation of `a >>> b : α`. See `HShiftRight`. -/
  shiftRight : α → α → α

@[default_instance]
instance [Add α] : HAdd α α α where
  hAdd a b := Add.add a b

@[default_instance]
instance [Sub α] : HSub α α α where
  hSub a b := Sub.sub a b

@[default_instance]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

@[default_instance]
instance [Div α] : HDiv α α α where
  hDiv a b := Div.div a b

@[default_instance]
instance [Mod α] : HMod α α α where
  hMod a b := Mod.mod a b

@[default_instance]
instance [Pow α β] : HPow α β α where
  hPow a b := Pow.pow a b

@[default_instance]
instance [Append α] : HAppend α α α where
  hAppend a b := Append.append a b

@[default_instance]
instance [OrElse α] : HOrElse α α α where
  hOrElse a b := OrElse.orElse a b

@[default_instance]
instance [AndThen α] : HAndThen α α α where
  hAndThen a b := AndThen.andThen a b

@[default_instance]
instance [AndOp α] : HAnd α α α where
  hAnd a b := AndOp.and a b

@[default_instance]
instance [Xor α] : HXor α α α where
  hXor a b := Xor.xor a b

@[default_instance]
instance [OrOp α] : HOr α α α where
  hOr a b := OrOp.or a b

@[default_instance]
instance [ShiftLeft α] : HShiftLeft α α α where
  hShiftLeft a b := ShiftLeft.shiftLeft a b

@[default_instance]
instance [ShiftRight α] : HShiftRight α α α where
  hShiftRight a b := ShiftRight.shiftRight a b

open HAdd (hAdd)
open HMul (hMul)
open HPow (hPow)
open HAppend (hAppend)

/--
The typeclass behind the notation `a ∈ s : Prop` where `a : α`, `s : γ`.
Because `α` is an `outParam`, the "container type" `γ` determines the type
of the elements of the container.
-/
class Membership (α : outParam (Type u)) (γ : Type v) where
  /-- The membership relation `a ∈ s : Prop` where `a : α`, `s : γ`. -/
  mem : α → γ → Prop

set_option bootstrap.genMatcherCode false in
/--
Addition of natural numbers.
This definition is overridden in both the kernel and the compiler to efficiently
evaluate using the "bignum" representation (see `Nat`). The definition provided
here is the logical model (and it is soundness-critical that they coincide).
-/
@[extern "lean_nat_add"]
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

theorem add_comm : ∀ (n m : Nat), Eq (Nat.add n m) (Nat.add m n)
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, succ m => _