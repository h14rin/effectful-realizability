/-
Copyright (c) 2026 Rinta Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rinta Yamada
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.Order.Hom.Basic
import EffectfulRealizability.Order

open CategoryTheory

structure CatHeytingPrealgebra where
  carrier : Type*
  [inst : HeytingPrealgebra carrier]

instance : CoeSort CatHeytingPrealgebra (Type*) where
  coe A := A.carrier

instance (A : CatHeytingPrealgebra) : HeytingPrealgebra A :=
  A.inst

instance instCategory : Category CatHeytingPrealgebra where
  Hom A B := OrderHom A B
  id A := OrderHom.id
  comp f g := OrderHom.comp g f

#print OrderHom.comp

class PreorderEnrichedCategory (C : Type*) extends Category C where
  hom_le {X Y : C} : (Hom X Y) → (Hom X Y) → Prop
  hom_le_refl {X Y : C} (f : Hom X Y) : hom_le f f
  hom_le_trans {X Y : C} (f g h : Hom X Y) :
    hom_le f g → hom_le g h → hom_le f h
  comp_mono {X Y Z : C} (f g : Hom X Y) (h k : Hom Y Z) :
    hom_le f g → hom_le h k → hom_le (comp f h) (comp g k)

instance instCatHeytingPrealgebraPreorderEnriched :
    PreorderEnrichedCategory CatHeytingPrealgebra where
  hom_le {X Y} f g    := ∀ x : X, (f.toFun x)  ≤ (g.toFun x)
  hom_le_refl {X Y} f := by simp
  hom_le_trans {X Y } f g h := by
    intros f_le_g g_le_h x
    exact le_trans (f_le_g x) (g_le_h x)
  comp_mono {X Y Z} f g h k := by
    intros f_le_g h_le_k x
    /- have comp_comm_fh : (f ≫ h).toFun x = h.toFun (f.toFun x) := by -/
    /-   rfl -/
    /- have comp_comm_gk : (g ≫ k).toFun x = k.toFun (g.toFun x) := by -/
    /-   rfl -/
    /- rw [comp_comm_fh, comp_comm_gk] -/
    have qhk {y y' : Y} : y ≤ y' → (h.toFun y) ≤ (k.toFun y') := by
      intro hy
      exact OrderHom.apply_mono h_le_k hy
    apply qhk (y := f.toFun x) (y' := g.toFun x)
    exact f_le_g x

abbrev isomorphic [instC : PreorderEnrichedCategory C] {X Y : C}
    (f g : instC.Hom X Y) : Prop :=
  instC.hom_le f g ∧ instC.hom_le g f

notation f "≃" g => isomorphic f g

structure PreorderPseudofunctor (C : Type*) (D : Type*)
    [instC : Category C] [instD : PreorderEnrichedCategory D] where
  obj : C → D
  map {X Y : C}   : (instC.Hom X Y) → instD.Hom (obj X) (obj Y)
  map_id (X : C)  : (map (instC.id X)) ≃ (instD.id (obj X))
  assoc {X Y Z : C} (f : instC.Hom X Y) (g : instC.Hom Y Z) :
    map (f ≫ g) ≃ (map f ≫ map g)
