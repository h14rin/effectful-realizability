/-
Copyright (c) 2026 Rinta Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rinta Yamada
-/

import Mathlib.Data.Set.Basic
import EffectfulRealizability.Order.Prelattice
import EffectfulRealizability.Order.HeytingPrealgebra

universe u v

class EvidencedFrame (Φ : Type u) (E : outParam (Type v)) where
  /-- Evidence relation -/
  ev : Φ -> E -> Φ -> Prop

  /-- Reflexivity -/
  e_id  : E
  ev_id : ∀ φ : Φ, ev φ e_id φ

  /-- Transitivity -/
  comp    : E -> E -> E
  ev_comp : ∀ {φ1 φ2 φ3 : Φ} {e e' : E},
    ev φ1 e φ2 -> ev φ2 e' φ3 -> ev φ1 (comp e e') φ3

  /-- Top -/
  top     : Φ
  e_top   : E
  ev_top  : ∀ φ : Φ, ev φ e_top top

  /-- Conjunction -/
  conj    : Φ -> Φ -> Φ
  pair    : E -> E -> E
  e_fst   : E
  e_snd   : E
  ev_fst  : ∀ φ1 φ2 : Φ, ev (conj φ1 φ2) e_fst φ1
  ev_snd  : ∀ φ1 φ2 : Φ, ev (conj φ1 φ2) e_snd φ2
  ev_pair : ∀ {φ ψ1 ψ2 : Φ} {e1 e2 : E},
    ev φ e1 ψ1 -> ev φ e2 ψ2 -> ev φ (pair e1 e2) (conj ψ1 ψ2)

  /-- Universal implication -/
  uimp      : Φ -> Set Φ -> Φ
  curry     : E -> E
  e_eval    : E
  ev_eval   : ∀ {φ : Φ} {Ψ : Set Φ} {ψ : Φ},
    ψ ∈ Ψ -> ev (conj (uimp φ Ψ) φ) e_eval ψ
  ev_curry  : ∀ {φ1 φ2 : Φ} {Ψ : Set Φ} {e : E},
    (∀ ψ ∈ Ψ, ev (conj φ1 φ2) e ψ) -> ev φ1 (curry e) (uimp φ2 Ψ)


/-- trivial example -/
instance trivialEF : EvidencedFrame Unit Unit where
  ev _ _ _ := True

  e_id    := ()
  ev_id _ := trivial

  comp _ _    := ()
  ev_comp _ _ := trivial

  top       := ()
  e_top     := ()
  ev_top _  := trivial

  conj _ _    := ()
  pair _ _    := ()
  e_fst       := ()
  e_snd       := ()
  ev_fst _ _  := trivial
  ev_snd _ _  := trivial
  ev_pair _ _ := trivial

  uimp _ _    := ()
  curry _     := ()
  e_eval      := ()
  ev_eval _   := trivial
  ev_curry _  := trivial

variable {Φ E : Type*} [EvidencedFrame Φ E]
export EvidencedFrame (ev e_id ev_id comp ev_comp top e_top ev_top
  conj pair e_fst e_snd ev_fst ev_snd ev_pair
  uimp curry e_eval ev_eval ev_curry)

-- Abbreviations
abbrev imp (φ ψ : Φ) : Φ
  := uimp φ {ψ}
abbrev iff (φ ψ : Φ) : Φ
  := conj (imp φ ψ) (imp ψ φ)
abbrev prod (Ψ : Set Φ) : Φ
  := uimp top Ψ
abbrev bot : Φ
  := prod (Set.univ : Set Φ)
abbrev disj (φ ψ : Φ) : Φ
  := prod (Set.range (fun χ =>
    imp (conj (imp φ χ) (imp ψ χ)) χ
  ))
abbrev coprod (Ψ : Set Φ) : Φ
  := prod (Set.range (fun φ =>
    imp (prod ((fun ψ => imp ψ φ) '' Ψ)) φ
  ))

notation:60 φ:60 "∧" ψ:60 => conj φ ψ
notation:60 φ:60 "∨" ψ:61 => disj φ ψ
notation:50 φ:51 "⊃" ψ:50 => imp φ ψ
notation:50 φ:51 "⊃" Ψ:50 => uimp φ Ψ
notation:40 "∏" Ψ => prod Ψ
notation:40 "⨿" Ψ => coprod Ψ
notation:30 φ "-[" e "]->" ψ => ev φ e ψ
notation:50 e₁:50 "++" e₂:51 => comp e₁ e₂
notation:50 e₁:50 "++" e₂:51 "in" Φ => comp Φ e₁ e₂
notation:60 "λ" e => curry e

-- Order
def stdLE (φ ψ : Φ) : Prop :=
  ∃ e : E, φ -[e]-> ψ

instance EfPropLE : LE Φ where
  le φ ψ := stdLE φ ψ

instance EfPropPreorder : Preorder Φ where
  le        := stdLE
  /- le_refl   := fun φ : Φ => ⟨e_id Φ, ev_id φ⟩ -/
  le_refl   := by
    intro φ
    exact ⟨e_id Φ, ev_id φ⟩
  le_trans  := by
    intros φ1 φ2 φ3 le1 le2
    obtain ⟨e1, h1⟩ := le1
    obtain ⟨e2, h2⟩ := le2
    exact ⟨e1 ++ e2 in Φ, ev_comp h1 h2⟩

theorem top_is_greatest : ∀ φ : Φ, φ ≤ top := by
  intro φ
  exists e_top Φ
  exact ev_top φ

instance EfPropTop : Top Φ where
  top := top

theorem bot_is_least : ∀ φ : Φ, bot ≤ φ := by
  intro φ
  unfold bot prod
  exists (pair Φ (e_id Φ) (e_top Φ)) ++ (e_eval Φ) in Φ
  let Univ : Set Φ := Set.univ
  have h1 : ev (uimp ⊤ Univ) (pair Φ (e_id Φ) (e_top Φ)) ((uimp ⊤ Univ) ∧ top) :=
    ev_pair (ev_id (uimp top Univ)) (ev_top (uimp top Univ))
  have univ_mem : ∀ ψ : Φ, ψ ∈ Univ := by
    rw [<- @Set.eq_univ_iff_forall Φ Univ]
  have φ_mem : φ ∈ Univ := univ_mem φ
  have h2 : ev (conj (uimp top Univ) top) (e_eval Φ) φ := ev_eval φ_mem
  exact ev_comp h1 h2

instance EfPropBot : Bot Φ where
  bot := bot

theorem conj_is_meet : ∀ {φ ψ : Φ}, isMeetOf φ ψ (conj φ ψ) := by
  unfold isMeetOf 
  intros φ ψ χ
  constructor
  case mp =>
    intro h
    obtain ⟨e, h⟩ := h
    constructor
    case left =>
      exists comp Φ e (e_fst Φ)
      have h_fst : ev (conj φ ψ) (e_fst Φ) φ := ev_fst φ ψ
      exact ev_comp h h_fst
    case right =>
      exists comp Φ e (e_snd Φ)
      have h_snd : ev (conj φ ψ) (e_snd Φ) ψ := ev_snd φ ψ
      exact ev_comp h h_snd
  case mpr =>
    intro ⟨⟨e1, h1⟩, ⟨e2, h2⟩⟩
    exact ⟨pair Φ e1 e2, ev_pair h1 h2⟩

lemma or_intro_l : ∀ {φ ψ : Φ}, φ ≤ (φ ∨ ψ) := by
  intros φ ψ
  unfold disj prod
  let p (χ : Φ) : Φ := imp ((imp φ χ) ∧ (imp ψ χ)) χ
  let ext_imp := comp Φ (e_snd Φ) (e_fst Φ)
  let ext_phi := comp Φ (e_fst Φ) (e_fst Φ)
  let e3 := pair Φ ext_imp ext_phi
  let e4 := e_eval Φ
  let e2 := comp Φ e3 e4
  let e1 := curry Φ e2
  change φ ≤ (uimp top (Set.range p))
  have q1 : ∀ α : Φ, α ∈ (Set.range p) -> (φ ∧ ⊤) -[e1]-> α := by
    intros α α_mem
    have α_form : ∃ χ : Φ, (p χ) = α := (Set.mem_range).mp α_mem
    obtain ⟨χ, eq⟩ := α_form
    rewrite [<- eq]
    unfold p
    have q2 : ((φ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[e2]-> χ := by
      have q3 : ((φ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[e3]-> ((imp φ χ) ∧ φ) := by
        have q3_1 : ((φ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[ext_imp]-> (imp φ χ) := by
          exact ev_comp (ev_snd (φ ∧ ⊤) ((imp φ χ) ∧ (imp ψ χ))) (ev_fst (imp φ χ) (imp ψ χ))
        have q3_2 : ((φ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[ext_phi]-> φ := by
          exact ev_comp (ev_fst (φ ∧ ⊤) ((imp φ χ) ∧ (imp ψ χ))) (ev_fst φ ⊤)
        exact ev_pair q3_1 q3_2
      have q4 : ((imp φ χ) ∧ φ) -[e4]-> χ := by
        exact ev_eval rfl
      exact ev_comp q3 q4
    have χ_mem : χ ∈ ({χ} : Set Φ) := by rfl
    apply ev_curry
    intro ψ1 ψ1_mem
    rw [ψ1_mem]
    exact q2
  exists curry Φ (e1)
  apply ev_curry
  intros ψ ψ_mem
  exact q1 ψ ψ_mem

lemma or_intro_r : ∀ {φ ψ : Φ}, ψ ≤ (φ ∨ ψ) := by
  intros φ ψ
  unfold disj prod
  let p (χ : Φ) : Φ := imp ((imp φ χ) ∧ (imp ψ χ)) χ
  let ext_imp := comp Φ (e_snd Φ) (e_snd Φ)
  let ext_psi := comp Φ (e_fst Φ) (e_fst Φ)
  let e3 := pair Φ ext_imp ext_psi
  let e4 := e_eval Φ
  let e2 := comp Φ e3 e4
  let e1 := curry Φ e2
  change ψ ≤ (uimp top (Set.range p))
  have q1 : ∀ α : Φ, α ∈ (Set.range p) -> (ψ ∧ ⊤) -[e1]-> α := by
    intros α α_mem
    have α_form : ∃ χ : Φ, (p χ) = α := (Set.mem_range).mp α_mem
    obtain ⟨χ, eq⟩ := α_form
    rewrite [<- eq]
    unfold p
    have q2 : ((ψ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[e2]-> χ := by
      have q3 : ((ψ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[e3]-> ((imp ψ χ) ∧ ψ) := by
        have q3_1 : ((ψ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[ext_imp]-> (imp ψ χ) := by
          exact ev_comp (ev_snd (ψ ∧ ⊤) ((imp φ χ) ∧ (imp ψ χ))) (ev_snd (imp φ χ) (imp ψ χ))
        have q3_2 : ((ψ ∧ ⊤) ∧  ((imp φ χ) ∧ (imp ψ χ))) -[ext_psi]-> ψ := by
          exact ev_comp (ev_fst (ψ ∧ ⊤) ((imp φ χ) ∧ (imp ψ χ))) (ev_fst ψ ⊤)
        exact ev_pair q3_1 q3_2
      have q4 : ((imp ψ χ) ∧ ψ) -[e4]-> χ := by
        exact ev_eval rfl
      exact ev_comp q3 q4
    have χ_mem : χ ∈ ({χ} : Set Φ) := by rfl
    apply ev_curry
    intro ψ1 ψ1_mem
    rw [ψ1_mem]
    exact q2
  exists curry Φ (e1)
  apply ev_curry
  intros ψ ψ_mem
  exact q1 ψ ψ_mem

theorem disj_is_join : ∀ {φ ψ : Φ}, isJoinOf φ ψ (disj φ ψ) := by
  unfold isJoinOf 
  /- unfold disj prod -/
  intros φ ψ χ
  let p (χ : Φ) : Φ := imp ((imp φ χ) ∧ (imp ψ χ)) χ
  constructor
  case mp =>
    intro le
    constructor 
    case left =>
      exact le_trans or_intro_l le
    case right =>
      exact le_trans or_intro_r le
  case mpr =>
    intro le
    obtain ⟨φ_le, ψ_le⟩ := le
    obtain ⟨e_φ, h_φ⟩ := φ_le
    obtain ⟨e_ψ, h_ψ⟩ := ψ_le
    change (uimp ⊤ (Set.range p)) ≤ χ
    let e_inner_φ : E := comp Φ (e_snd Φ) e_φ
    let e_imp_φ : E := curry Φ e_inner_φ
    have q2_φ : (φ ∨ ψ) -[e_imp_φ]-> (imp φ χ) := by
      apply ev_curry
      intros ψ1 ψ1_mem
      rw [ψ1_mem]
      apply ev_comp (φ2 := φ)
      · exact ev_snd (φ ∨ ψ) φ
      · exact h_φ
    let e_inner_ψ : E := comp Φ (e_snd Φ) e_ψ
    let e_imp_ψ : E := curry Φ e_inner_ψ
    have q2_ψ : (φ ∨ ψ) -[e_imp_ψ]-> (imp ψ χ) := by
      apply ev_curry
      intros ψ1 ψ1_mem
      rw [ψ1_mem]
      apply ev_comp (φ2 := ψ)
      · exact ev_snd (φ ∨ ψ) ψ
      · exact h_ψ
    let e_args : E := pair Φ e_imp_φ e_imp_ψ
    have q3 : (φ ∨ ψ) -[e_args]-> ((imp φ χ) ∧ (imp ψ χ)):= ev_pair q2_φ q2_ψ
    let e_top_pair :E := pair Φ (e_id Φ) (e_top Φ)
    have q4 : (φ ∨ ψ) -[e_top_pair]-> ((φ ∨ ψ) ∧ ⊤) := ev_pair (ev_id (φ ∨ ψ)) (ev_top (φ ∨ ψ))
    let e_top_p := e_eval Φ
    have q5 : ((φ ∨ ψ) ∧ ⊤) -[e_top_p]-> (p χ) := by
      apply ev_eval
      exact (Set.mem_range_self χ)
    let e_p := comp Φ e_top_pair e_top_p
    have q6 : (φ ∨ ψ) -[e_p]-> (p χ) := by
      apply ev_comp q4 q5
    let e_p_args := pair Φ e_p e_args
    have q7 : (φ ∨ ψ) -[e_p_args]-> ((p χ) ∧ ((imp φ χ) ∧ (imp ψ χ))) := by
      apply ev_pair q6 q3
    let e_p_args_eval := e_eval Φ
    have q8 : ((p χ) ∧ ((imp φ χ) ∧ (imp ψ χ))) -[e_p_args_eval]-> χ := by
      apply ev_eval
      exact rfl
    exists (comp Φ e_p_args e_p_args_eval)
    apply ev_comp q7 q8

lemma conj_comm : ∀ {φ ψ : Φ}, φ ∧ ψ ≃ ψ ∧ φ := by
  intros φ ψ
  constructor
  case left =>
    exists pair Φ (e_snd Φ) (e_fst Φ)
    exact ev_pair (ev_snd φ ψ) (ev_fst φ ψ)
  case right =>
    exists pair Φ (e_snd Φ) (e_fst Φ)
    exact ev_pair (ev_snd ψ φ) (ev_fst ψ φ)

theorem imp_is_himp : ∀ {φ ψ : Φ}, isHimpOf φ ψ (imp φ ψ) := by
  unfold isHimpOf
  intros φ ψ
  constructor
  case left =>
    intros a hm
    have φ_imp_meet : isMeetOf φ (imp φ ψ) (φ ∧ (imp φ ψ)) := conj_is_meet
    have iso : a ≃ φ ∧ (imp φ ψ) := by
      apply meet_iso φ (imp φ ψ) a (φ ∧ (imp φ ψ))
      exact ⟨hm, φ_imp_meet⟩
    have φ_le : (φ ∧ (imp φ ψ)) ≤ ψ := by
      exists comp Φ (pair Φ (e_snd Φ) (e_fst Φ)) (e_eval Φ)
      apply ev_comp (φ2 := (imp φ ψ) ∧ φ)
      · exact ev_pair (ev_snd φ (imp φ ψ)) (ev_fst φ (imp φ ψ))
      · apply ev_eval
        rfl
    exact le_trans (iso.left) φ_le
  case right =>
    intros a ha
    let a_and_φ := ha (a ∧ φ)
    have trans_mid : ((a ∧ φ) ≤ ψ) -> (a ≤ (imp φ ψ)) := by
      intro h
      obtain ⟨e, g⟩ := h
      exists curry Φ e
      apply ev_curry
      intro ψ1 ψ1_mem
      rw [ψ1_mem]
      exact g
    apply trans_mid
    apply a_and_φ
    have φ_a_iso_a_φ : (φ ∧ a) ≃ (a ∧ φ)  := conj_comm
    apply (meet_iso_rw φ a (φ ∧ a) (a ∧ φ))
    constructor
    case left =>
      exact conj_is_meet
    case right =>
      exact φ_a_iso_a_φ

lemma and_elim_l : ∀ {φ ψ : Φ}, (φ ∧ ψ) ≤ φ := by
  intro φ ψ
  exists e_fst Φ
  exact ev_fst φ ψ

lemma and_elim_r : ∀ {φ ψ : Φ}, (φ ∧ ψ) ≤ ψ := by
  intro φ ψ
  exists e_snd Φ
  exact ev_snd φ ψ

instance EfPropMeet : Meet Φ where
  meet := conj
  l_bound := by
    intros a b
    constructor
    case left => 
      exact and_elim_l
    case right =>
      exact and_elim_r
  maximality := by
    intros a b l
    have meet_ab : isMeetOf a b (conj a b) := conj_is_meet
    unfold isMeetOf at meet_ab
    exact (meet_ab l).mpr

instance EfPropJoin : Join Φ where
  join := disj
  u_bound := by
    intros a b
    constructor
    case left =>
      exact or_intro_l
    case right =>
      exact or_intro_r
  minimality := by
    intros a b u
    have join_ab : isJoinOf a b (disj a b) := disj_is_join
    unfold isJoinOf at join_ab
    exact (join_ab u).mpr

instance EfPropPrelattice : Prelattice Φ where
  le_top := by
    intro a
    exists e_top Φ
    exact ev_top a
  bot_le := by
    intro a
    have q1 : ⊥ ≤ ((⊥ : Φ) ∧ ⊤) := by
      exists pair Φ (e_id Φ) (e_top Φ)
      exact ev_pair (ev_id (⊥ : Φ)) (ev_top (⊥ : Φ))
    have q2 : ((⊥ : Φ) ∧ ⊤) ≤ a := by
      have a_mem : a ∈ (Set.univ : Set Φ) := trivial
      exists (e_eval Φ)
      exact (ev_eval (Set.mem_univ a))
    exact le_trans q1 q2

instance EfPropHImp : HImp Φ where
  himp := imp

instance EfPropHeytingPrealgebra : HeytingPrealgebra Φ where
  himp_maximality := by
    intros a b c hm
    have himp_ab : isHimpOf a b (imp a b) := imp_is_himp
    unfold isHimpOf at himp_ab
    obtain ⟨h1, h2⟩ := himp_ab
    apply h2 c
    intro d meet_acd
    unfold isMeetOf at meet_acd
    have d_le_a : d ≤ a := ((meet_acd d).mp (le_refl d)).left
    have d_le_c : d ≤ c := ((meet_acd d).mp (le_refl d)).right
    have d_le_ca : d ≤ (c ⊓ a) := Meet.maximality ⟨d_le_c, d_le_a⟩
    exact le_trans d_le_ca hm
