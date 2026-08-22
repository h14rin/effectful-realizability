/-
Copyright (c) 2026 Rinta Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rinta Yamada
-/

import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import EffectfulRealizability.Category.Pseudofunctor

/-!
# Tripos

This file introduces the basic definition of a tripos.

A tripos is a pseudofunctor `Setᵒᵖ ⇒ CatHP` enjoying logical properties in a certain sence.
More generally, one can define a `C`-tripos `Cᵒᵖ ⇒ CatHP` for a finitely complete category `C`.
However, we consider only the `Set`-tripos, which represents the minimal necessary concept.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u

def CatType := Type u

instance instCatType : Category CatType := types
instance instCatTypeOp : Category CatTypeᵒᵖ := Category.opposite

variable {X Y : CatTypeᵒᵖ} {f : TypeCat.Hom (unop X) (unop Y)}

class TypeTripos extends PreorderPseudofunctor CatTypeᵒᵖ CatHP where
  hasLeftAdjoint : ∀ {X Y : CatTypeᵒᵖ} {f : instCatTypeOp.Hom Y X},
                   ∃ e_f : OrderHom (obj X) (obj Y), ∀ {x : obj X} {y : obj Y},
                    (x ≤ ((map f).toFun y)) ↔  ((e_f x) ≤ y)
  hasRightAdjoint : ∀ {X Y : CatTypeᵒᵖ} {f : instCatTypeOp.Hom Y X},
                   ∃ a_f : OrderHom (obj X) (obj Y), ∀ {x : obj X} {y : obj Y},
                    (x ≤ ((map f).toFun y)) ↔  ((e_f x) ≤ y)

  -- TODO
