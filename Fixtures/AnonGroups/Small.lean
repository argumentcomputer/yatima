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