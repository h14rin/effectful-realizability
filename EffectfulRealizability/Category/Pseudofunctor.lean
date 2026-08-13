/-
Copyright (c) 2026 Rinta Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rinta Yamada
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import EffectfulRealizability.Order

structure CatHeytingPrealgebra where
  carrier : Type*
  [inst : HeytingPrealgebra carrier]

instance : CoeSort CatHeytingPrealgebra (Type*) where
  coe H := H.carrier

instance (H : CatHeytingPrealgebra) : HeytingPrealgebra H :=
  H.inst
