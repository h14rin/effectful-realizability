/-
Copyright (c) 2026 Rinta Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rinta Yamada
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed

set_option linter.style.header false
open CategoryTheory
open CategoryTheory.Limits
universe u v

class CartesianClosedCategory (C : Type u)
    extends Category C, HasFiniteProducts C, HasTerminal C where
  -- TODO

class CccTripos (C : Type u) where
  -- TODO
