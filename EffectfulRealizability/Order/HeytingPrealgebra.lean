/-
Copyright (c) 2026 Rinta Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rinta Yamada
-/

import Mathlib.Order.Basic
import Mathlib.Order.Notation
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Monotone.Defs
import EffectfulRealizability.Order.Prelattice

/-!
# HeytingPrealgebra

This file provides elementary definitions and theorems for ordered sets,
especially for prelattices and Heyting prealgebras.

Let `a` and `b` be elements of a preorder.
* The join `a ⊔ b` of `a` and `b` is the least upper bound.
* The meet `a ⊓ b` of `a` and `b` is the greatest lower bound.
-/

class HeytingPrealgebra (P : Type*) extends Prelattice P, HImp P where
  himp_maximality : ∀ {a b c : P}, ((c ⊓ a) ≤ b) → (c ≤ (a ⇨ b))

def preservesJoin [Join P] [Join Q] (f : P → Q) : Prop :=
  ∀ x y : P, (f (x ⊔ y)) ≃ ((f x) ⊔ (f y))

def preservesMeet [Meet P] [Meet Q] (f : P → Q) : Prop :=
  ∀ x y : P, (f (x ⊓ y)) ≃ ((f x) ⊓ (f y))

def preservesHImp [HeytingPrealgebra P] [HeytingPrealgebra Q] (f : P → Q) : Prop :=
  ∀ x y : P, (f (x ⇨ y)) ≃ ((f x) ⇨ (f y))

def HpMorphism [HeytingPrealgebra A] [HeytingPrealgebra B] (f : A → B) : Prop :=
  Monotone f ∧ preservesJoin f ∧ preservesMeet f ∧ preservesHImp f

structure HpHom (A B : Type*) [HeytingPrealgebra A] [HeytingPrealgebra B] extends OrderHom A B where
  map_join : preservesJoin toFun
  map_meet : preservesMeet toFun
  map_himp : preservesHImp toFun

namespace HpHom

variable [HeytingPrealgebra A] [HeytingPrealgebra B] [HeytingPrealgebra C]

@[simps -fullyApplied]
def id : HpHom A A := {
  toFun := fun x ↦ x
  monotone' := by
    unfold Monotone
    intros a b hab
    exact hab
  map_join := by
    unfold preservesJoin 
    intros a b
    constructor
    case left =>
      rfl
    case right =>
      rfl
  map_meet := by
    unfold preservesMeet
    intros a b
    constructor
    case left =>
      rfl
    case right =>
      rfl
  map_himp := by
    unfold preservesHImp
    intro a b
    constructor
    case left =>
      rfl
    case right =>
      rfl
}

@[simps -fullyApplied]
def comp (g : HpHom B C) (f : HpHom A B) : HpHom A C := {
  toFun := g.toFun ∘ f.toFun
  monotone' := by
    unfold Monotone
    intros a b hab
    apply g.monotone'
    apply f.monotone'
    exact hab
  map_join := by
    unfold preservesJoin
    intro a b
    have hf : f.toFun (a ⊔ b) ≃ f.toFun a ⊔ f.toFun b := f.map_join a b
    have hg : g.toFun ((f.toFun a) ⊔ (f.toFun b)) ≃ (g.toFun (f.toFun a)) ⊔ (g.toFun (f.toFun b)) :=
      g.map_join (f.toFun a) (f.toFun b)
    have gf_iso : g.toFun (f.toFun (a ⊔ b)) ≃ g.toFun (f.toFun a ⊔ f.toFun b) := by
      constructor
      case left =>
        apply g.monotone'
        exact (f.map_join a b).left
      case right =>
        apply g.monotone'
        exact (f.map_join a b).right
    constructor
    case left =>
      apply le_trans gf_iso.left hg.left
    case right =>
      apply le_trans hg.right  gf_iso.right
  map_meet := by
    intros a b
    have hf : f.toFun (a ⊓ b) ≃ f.toFun a ⊓ f.toFun b := f.map_meet a b
    have hg : g.toFun ((f.toFun a) ⊓ (f.toFun b)) ≃ (g.toFun (f.toFun a)) ⊓ (g.toFun (f.toFun b)) :=
      g.map_meet (f.toFun a) (f.toFun b)
    have gf_iso : g.toFun (f.toFun (a ⊓ b)) ≃ g.toFun (f.toFun a ⊓ f.toFun b) := by
      constructor
      case left =>
        apply g.monotone'
        exact (f.map_meet a b).left
      case right =>
        apply g.monotone'
        exact (f.map_meet a b).right
    constructor
    case left =>
      apply le_trans gf_iso.left hg.left
    case right =>
      apply le_trans hg.right  gf_iso.right
  map_himp := by
    intros a b
    have hf : f.toFun (a ⇨ b) ≃ f.toFun a ⇨ f.toFun b := f.map_himp a b
    have hg : g.toFun ((f.toFun a) ⇨ (f.toFun b)) ≃ (g.toFun (f.toFun a)) ⇨ (g.toFun (f.toFun b)) :=
      g.map_himp (f.toFun a) (f.toFun b)
    have gf_iso : g.toFun (f.toFun (a ⇨ b)) ≃ g.toFun (f.toFun a ⇨ f.toFun b) := by
      constructor
      case left =>
        apply g.monotone'
        exact (f.map_himp a b).left
      case right =>
        apply g.monotone'
        exact (f.map_himp a b).right
    constructor
    case left =>
      apply le_trans gf_iso.left hg.left
    case right =>
      apply le_trans hg.right  gf_iso.right
}

end HpHom
