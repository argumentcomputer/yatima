/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import TypeChecker.Init.Meta
import TypeChecker.Init.Data.ToString.Basic

syntax:max "s!" interpolatedStr(term) : term

macro_rules
  | `(s! $interpStr) => do interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
