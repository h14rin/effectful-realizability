/-
Copyright (c) 2026 Rinta Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rinta Yamada
-/

import Mathlib.Order.Basic
import Mathlib.Order.Notation
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Monotone.Defs

abbrev isJoinOf [Preorder P] (φ ψ j : P) : Prop := ∀ χ : P, j ≤ χ ↔ ((φ ≤ χ) ∧ (ψ ≤ χ))
abbrev isJoinOfAlt [Preorder P] (φ ψ j : P) : Prop :=
  ((φ ≤ j) ∧ (ψ ≤ j)) ∧ ∀ χ : P, ((φ ≤ χ) ∧ (ψ ≤ χ) -> j ≤ χ)
abbrev isMeetOf [Preorder P] (φ ψ m : P) : Prop := ∀ χ : P, χ ≤ m ↔ ((χ ≤ φ) ∧ (χ ≤ ψ))
abbrev isHimpOf [Preorder P] (φ ψ i : P) : Prop :=
  (∀ a : P, isMeetOf φ i a -> a ≤ ψ) ∧ (∀ χ : P, (∀ a : P, isMeetOf φ χ a -> a ≤ ψ) → χ ≤ i)

example [Preorder P] : ∀ φ ψ j : P, isJoinOf φ ψ j ↔ isJoinOfAlt φ ψ j := by
  intros φ ψ j
  unfold isJoinOf isJoinOfAlt
  constructor
  case mp =>
    intro h
    constructor
    case left =>
      apply (h j).mp
      exact le_refl j
    case right =>
      intro χ
      exact (h χ).mpr
  case mpr =>
    intros h χ
    obtain ⟨h1, h2⟩ := h
    constructor
    case mp =>
      intro q
      constructor
      case left =>
        exact le_trans (h1.left) q
      case right =>
        exact le_trans (h1.right) q
    case mpr =>
      intro q
      apply (h2 χ)
      exact q

notation:30 p "≃" q => (p ≤ q) ∧ (q ≤ p)

theorem meet_iso [Preorder P] : ∀ φ ψ m n : P, isMeetOf φ ψ m ∧ isMeetOf φ ψ n -> m ≃ n := by
  intros φ ψ m n h
  obtain ⟨hm, hn⟩ := h
  unfold isMeetOf at hm hn
  constructor
  case left =>
    apply (hn m).mpr
    apply (hm m).mp
    exact le_refl m
  case right =>
    apply (hm n).mpr
    apply (hn n).mp
    exact le_refl n

theorem meet_iso_rw [Preorder P] : ∀ φ ψ m n : P, (isMeetOf φ ψ m) ∧ (m ≃ n) -> isMeetOf φ ψ n := by
  intros φ ψ m n h
  obtain ⟨hm, ⟨hmn, hnm⟩⟩ := h
  unfold isMeetOf
  unfold isMeetOf at hm
  intro χ
  constructor
  case mp =>
    intro χ_le_n
    apply (hm χ).mp
    exact le_trans χ_le_n hnm
  case mpr =>
    intro χ_le_φψ
    apply le_trans ((hm χ).mpr χ_le_φψ) hmn

theorem join_iso [Preorder P] : ∀ φ ψ j k : P, isJoinOf φ ψ j ∧ isJoinOf φ ψ k -> j ≃ k := by
  intros φ ψ j k h
  obtain ⟨hj, hk⟩ := h
  unfold isJoinOf at hj hk
  constructor
  case left =>
    apply (hj k).mpr
    apply (hk k).mp
    exact le_refl k
  case right =>
    apply (hk j).mpr
    apply (hj j).mp
    exact le_refl j

theorem join_iso_rw [Preorder P] : ∀ φ ψ j k : P, (isJoinOf φ ψ j) ∧ (j ≃ k) -> isJoinOf φ ψ k := by
  intros φ ψ j k h
  obtain ⟨hj, ⟨hjk, hkj⟩⟩ := h
  unfold isJoinOf
  unfold isJoinOf at hj
  intro χ
  constructor
  case mp =>
    intro k_le_χ
    apply (hj χ).mp
    exact le_trans hjk k_le_χ
  case mpr =>
    intro φψ_le_χ
    apply le_trans hkj ((hj χ).mpr φψ_le_χ)

class Meet (P : Type*) extends Preorder P where
  meet : P → P → P
  l_bound     : ∀ {a b : P}, (meet a b ≤ a) ∧ (meet a b ≤ b)
  maximality  : ∀ {a b l : P}, ((l ≤ a) ∧ (l ≤ b)) → (l ≤ meet a b)

notation:70 a "⊓" b => Meet.meet a b 

theorem meet_le_l [Meet P] : ∀ {a b : P}, (a ⊓ b) ≤ a := by
  intros a b
  exact (Meet.l_bound (a := a) (b := b)).left

theorem meet_le_r [Meet P] : ∀ {a b : P}, (a ⊓ b) ≤ b := by
  intros a b
  exact (Meet.l_bound (a := a) (b := b)).right

theorem meet_coincide [Meet P] : ∀ {a b m : P}, isMeetOf a b m ↔ (m ≃ (a ⊓ b)) := by
  intros a b m
  constructor
  case mp =>
    intro habm
    unfold isMeetOf at habm
    constructor
    case left =>
      apply Meet.maximality
      exact (habm m).mp (le_refl m)
    case right =>
      apply (habm (a ⊓ b)).mpr
      exact ⟨meet_le_l, meet_le_r⟩
  case mpr =>
    intros h
    obtain ⟨habm, hmab⟩ := h
    unfold isMeetOf
    intro χ
    constructor
    case mp =>
      intro hχm
      let q := le_trans hχm habm
      exact ⟨le_trans q meet_le_l, le_trans q meet_le_r⟩
    case mpr =>
      intro hχab
      let q := Meet.maximality hχab
      exact le_trans q hmab

class Join (P : Type*) extends Preorder P where
  join : P → P → P
  u_bound     : ∀ {a b : P}, (a ≤ join a b) ∧ (b ≤ join a b)
  minimality  : ∀ {a b u : P}, ((a ≤ u) ∧ (b ≤ u)) → (join a b ≤ u)

notation:70 a "⊔" b => Join.join a b 

theorem l_le_join [Join P] : ∀ {a b : P}, a ≤ (a ⊔ b) := by
  intros a b
  exact (Join.u_bound (a := a) (b := b)).left

theorem r_le_join [Join P] : ∀ {a b : P}, b ≤ (a ⊔ b) := by
  intros a b
  exact (Join.u_bound (a := a) (b := b)).right

theorem join_coincide [Join P] : ∀ {a b j : P}, isJoinOf a b j ↔ (j ≃ (a ⊔ b)) := by
  intros a b j
  constructor
  case mp =>
    intro habj
    unfold isJoinOf at habj
    constructor
    case left =>
      apply (habj (a ⊔ b)).mpr
      exact Join.u_bound
    case right =>
      let q := (habj j).mp (le_refl j)
      exact Join.minimality q
  case mpr =>
    intros h
    obtain ⟨hjab, habj⟩ := h
    unfold isJoinOf
    intro χ
    constructor
    case mp =>
      intro hjχ
      let q := le_trans habj hjχ
      exact ⟨le_trans l_le_join q, le_trans r_le_join q⟩
    case mpr =>
      intro habχ
      let q := Join.minimality habχ
      exact le_trans hjab q

class Prelattice (P : Type*) extends Preorder P, Top P, Bot P, Meet P, Join P where
  le_top : ∀ a : P, a ≤ ⊤
  bot_le : ∀ a : P, ⊥ ≤ a

class HeytingPrealgebra (P : Type*) extends Prelattice P, HImp P where
  himp_maximality : ∀ {a b c : P}, ((c ⊓ a) ≤ b) → (c ≤ (a ⇨ b))
