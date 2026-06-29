/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.HFSets
import Peano.PeanoNat.Combinatorics.Pow

namespace CList

def sublists {α : Type} : PList α → PList (PList α)
  | .nil       => .cons .nil .nil
  | .cons a as =>
    let rest := sublists as
    rest ++ rest.map (.cons a ·)

/-- Toda sub-PList de `xs` es subconjunto de `mk xs`. -/
theorem sublists_subset
    (xs : PList CList) (zs : PList CList) (h : PList.Mem zs (sublists xs)) :
    subset (mk zs) (mk xs) = true := by
  induction xs generalizing zs with
  | nil =>
    simp only [sublists, PList.Mem_cons_iff, PList.not_mem_nil] at h
    rcases h with rfl | h
    · exact subset_nil _
    · exact absurd h (fun h => h)
  | cons x xs' ih =>
    simp only [sublists, PList.Mem_append, PList.Mem_map] at h
    rcases h with h_in_rest | ⟨ws, h_ws_in_rest, rfl⟩
    · exact subset_mono zs x xs' (ih zs h_in_rest)
    · rw [subset_cons, Bool.and_eq_true]
      constructor
      · rw [mem_cons, Bool.or_eq_true]; exact Or.inl (extEq_refl x)
      · exact subset_mono ws x xs' (ih ws h_ws_in_rest)

/-- `PList.filter P xs` est membre de `sublists xs`. -/
theorem filter_in_sublists {α : Type}
    (P : α → Bool) (xs : PList α) :
    PList.Mem (PList.filter P xs) (sublists xs) := by
  induction xs with
  | nil => exact PList.Mem.head
  | cons a as ih =>
    simp only [sublists, PList.filter, PList.Mem_append, PList.Mem_map]
    split
    · exact Or.inr ⟨PList.filter P as, ih, rfl⟩
    · exact Or.inl ih

/-- `fun z => mem z y` respeta la igualdad extensional. -/
theorem mem_right_respects_extEq (y : CList) : P_respects (fun z => mem z y) := by
  intro a b hab
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro ha; exact mem_of_extEq b a y (by rw [extEq_comm]; exact hab) ha
  · intro hb; exact mem_of_extEq a b y hab hb

-- ─────────────────────────────────────────────────────────────────
-- Lemmas for Cardinal: sublists properties
-- ─────────────────────────────────────────────────────────────────

private theorem sublists_plist_mem {α : Type} (xs zs : PList α) (y : α)
    (h_zs : PList.Mem zs (sublists xs)) (h_y : PList.Mem y zs) : PList.Mem y xs := by
  induction xs generalizing zs with
  | nil =>
    simp only [sublists] at h_zs
    cases h_zs with
    | head => exact absurd h_y (PList.not_mem_nil _)
    | tail h => exact absurd h (PList.not_mem_nil _)
  | cons x xs' ih =>
    simp only [sublists, PList.Mem_append, PList.Mem_map] at h_zs
    rcases h_zs with h_rest | ⟨ws, h_ws, rfl⟩
    · exact PList.Mem.tail (ih zs h_rest h_y)
    · cases h_y with
      | head => exact PList.Mem.head
      | tail h_y' => exact PList.Mem.tail (ih ws h_ws h_y')

private theorem plist_any_eq_false_of_all {α : Type} (p : α → Bool) (l : PList α)
    (h : ∀ x, PList.Mem x l → p x = false) : PList.any p l = false := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [PList.any_cons, Bool.or_eq_false_iff]
    exact ⟨h y PList.Mem.head, ih (fun z hz => h z (PList.Mem.tail hz))⟩

private theorem a_not_mem_sublist (a : CList) (as : PList CList)
    (ha : ∀ y, PList.Mem y as → extEq a y = false)
    (ws : PList CList) (h_ws : PList.Mem ws (sublists as)) :
    CList.mem a (CList.mk ws) = false := by
  rw [mem_eq_any]
  apply plist_any_eq_false_of_all
  intro z hz_ws
  exact ha z (sublists_plist_mem as ws z h_ws hz_ws)

private theorem cross_not_extEq (a : CList) (ws vs : PList CList)
    (ha_not_ws : CList.mem a (CList.mk ws) = false) :
    CList.extEq (CList.mk ws) (CList.mk (PList.cons a vs)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [extEq_def, Bool.and_eq_true] at h
  have ha_in_acons : CList.mem a (CList.mk (.cons a vs)) = true := by
    rw [mem_cons, Bool.or_eq_true]; exact Or.inl (extEq_refl a)
  have ha_in_ws : CList.mem a (CList.mk ws) = true :=
    (HFSet.subset_iff_forall_mem_clist _ _).mp h.2 a ha_in_acons
  simp [ha_not_ws] at ha_in_ws

private theorem nodup_append (l₁ l₂ : PList CList)
    (h₁ : Nodup l₁) (h₂ : Nodup l₂)
    (h_cross : ∀ x, PList.Mem x l₁ → ∀ y, PList.Mem y l₂ → extEq x y = false) :
    Nodup (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact h₂
  | cons x xs ih =>
    obtain ⟨hx_nd, hxs_nd⟩ := h₁
    simp only [PList.cons_append, Nodup]
    refine ⟨fun z hz => ?_, ih hxs_nd (fun a ha b hb => h_cross a (PList.Mem.tail ha) b hb)⟩
    rcases (PList.Mem_append z xs l₂).mp hz with hz_xs | hz_l₂
    · exact hx_nd z hz_xs
    · exact h_cross x PList.Mem.head z hz_l₂

private theorem nodup_map_cons_a (a : CList) (as : PList CList)
    (ha : ∀ y, PList.Mem y as → extEq a y = false)
    (l : PList (PList CList))
    (hl : ∀ ws, PList.Mem ws l → PList.Mem ws (sublists as))
    (h_nodup : Nodup (l.map CList.mk)) :
    Nodup (l.map (fun ws => CList.mk (PList.cons a ws))) := by
  induction l with
  | nil => simp [Nodup]
  | cons ws rest ih =>
    simp only [PList.map_cons, Nodup]
    obtain ⟨hws_nd, hrest_nd⟩ := h_nodup
    have hws_in := hl ws PList.Mem.head
    have ha_not_ws := a_not_mem_sublist a as ha ws hws_in
    refine ⟨fun z hz => ?_, ih (fun w hw => hl w (PList.Mem.tail hw)) hrest_nd⟩
    obtain ⟨vs, hvs_rest, rfl⟩ := (PList.Mem_map _ z _).mp hz
    have hvs_in := hl vs (PList.Mem.tail hvs_rest)
    have ha_not_vs := a_not_mem_sublist a as ha vs hvs_in
    have hws_vs_false : CList.extEq (CList.mk ws) (CList.mk vs) = false :=
      hws_nd (CList.mk vs) ((PList.Mem_map _ (CList.mk vs) _).mpr ⟨vs, hvs_rest, rfl⟩)
    rw [Bool.eq_false_iff]
    intro h_extEq
    have h_sub : CList.extEq (CList.mk ws) (CList.mk vs) = true := by
      rw [extEq_def, Bool.and_eq_true]
      rw [extEq_def, Bool.and_eq_true] at h_extEq
      obtain ⟨h12, h21⟩ := h_extEq
      constructor
      · rw [HFSet.subset_iff_forall_mem_clist]
        intro z hz_ws
        have hz_in := (HFSet.subset_iff_forall_mem_clist _ _).mp h12 z
          (by rw [mem_cons, Bool.or_eq_true]; exact Or.inr hz_ws)
        rw [mem_cons, Bool.or_eq_true] at hz_in
        rcases hz_in with heq_za | hmem
        · exact absurd (mem_of_extEq a z (CList.mk ws) (by rwa [extEq_comm]) hz_ws)
            (by simp [ha_not_ws])
        · exact hmem
      · rw [HFSet.subset_iff_forall_mem_clist]
        intro z hz_vs
        have hz_in := (HFSet.subset_iff_forall_mem_clist _ _).mp h21 z
          (by rw [mem_cons, Bool.or_eq_true]; exact Or.inr hz_vs)
        rw [mem_cons, Bool.or_eq_true] at hz_in
        rcases hz_in with heq_za | hmem
        · exact absurd (mem_of_extEq a z (CList.mk vs) (by rwa [extEq_comm]) hz_vs)
            (by simp [ha_not_vs])
        · exact hmem
    simp [hws_vs_false] at h_sub

private theorem sorted_tail' {a : CList} {l : PList CList}
    (h : Sorted (.cons a l)) : Sorted l :=
  match l with
  | .nil => trivial
  | .cons _ _ => h.2

theorem sublists_sorted (xs : PList CList) (hs : Sorted xs) :
    ∀ zs, PList.Mem zs (sublists xs) → Sorted zs := by
  induction xs with
  | nil =>
    intro zs hmem
    simp only [sublists] at hmem
    cases hmem with
    | head => exact trivial
    | tail h => exact absurd h (PList.not_mem_nil _)
  | cons a as ih =>
    have hs_as : Sorted as := sorted_tail' hs
    intro zs hmem
    simp only [sublists, PList.Mem_append, PList.Mem_map] at hmem
    rcases hmem with h_rest | ⟨ws, h_ws, rfl⟩
    · exact ih hs_as zs h_rest
    · cases ws with
      | nil => exact trivial
      | cons b rest =>
        constructor
        · exact sorted_head_lt_of_mem hs (sublists_plist_mem as (PList.cons b rest) b h_ws PList.Mem.head)
        · exact ih hs_as (PList.cons b rest) h_ws

theorem sublists_nodup (xs : PList CList) (hn : Nodup xs) :
    ∀ zs, PList.Mem zs (sublists xs) → Nodup zs := by
  induction xs with
  | nil =>
    intro zs hmem
    simp only [sublists] at hmem
    cases hmem with
    | head => exact trivial
    | tail h => exact absurd h (PList.not_mem_nil _)
  | cons a as ih =>
    obtain ⟨ha_nd, has_nd⟩ := hn
    intro zs hmem
    simp only [sublists, PList.Mem_append, PList.Mem_map] at hmem
    rcases hmem with h_rest | ⟨ws, h_ws, rfl⟩
    · exact ih has_nd zs h_rest
    · simp only [Nodup]
      refine ⟨fun y hy => ?_, ih has_nd ws h_ws⟩
      exact ha_nd y (sublists_plist_mem as ws y h_ws hy)

theorem sublists_norm (xs : PList CList) (hs : Sorted xs) (hn : Nodup xs)
    (hall : ∀ y, PList.Mem y xs → normalize y = y) :
    ∀ zs, PList.Mem zs (sublists xs) → normalize (CList.mk zs) = CList.mk zs := by
  intro zs h_zs
  apply normalize_mk_of_normalized_sorted_nodup
  · exact sublists_sorted xs hs zs h_zs
  · exact sublists_nodup xs hn zs h_zs
  · intro y hy_zs
    exact hall y (sublists_plist_mem xs zs y h_zs hy_zs)

theorem sublists_nodup_mk (xs : PList CList) (hn : Nodup xs) :
    Nodup ((sublists xs).map CList.mk) := by
  induction xs with
  | nil =>
    simp only [sublists, PList.map_cons, PList.map_nil, Nodup]
    exact ⟨fun y hy => absurd hy (PList.not_mem_nil _), trivial⟩
  | cons a as ih =>
    obtain ⟨ha_nd, has_nd⟩ := hn
    have ih_nodup := ih has_nd
    -- map mk (map (cons a) l) = map (fun ws => mk (cons a ws)) l
    have map_comp : ∀ (l : PList (PList CList)),
        PList.map CList.mk (PList.map (PList.cons a ·) l) =
        PList.map (fun ws => CList.mk (PList.cons a ws)) l := fun l => by
      induction l with
      | nil => rfl
      | cons h t ih' => simp only [PList.map_cons, ih']
    -- Split outer map over append, then fold composed map
    have eq_goal : PList.map CList.mk (sublists as ++ (sublists as).map (PList.cons a ·)) =
        PList.map CList.mk (sublists as) ++
        PList.map (fun ws => CList.mk (PList.cons a ws)) (sublists as) := by
      -- Prove map_append for ++ via induction (PList.map_append uses .append, not ++)
      have map_app : ∀ (l₁ l₂ : PList (PList CList)),
          PList.map CList.mk (l₁ ++ l₂) = PList.map CList.mk l₁ ++ PList.map CList.mk l₂ := by
        intro l₁ l₂
        induction l₁ with
        | nil => rfl
        | cons h t ih_t => simp only [PList.cons_append, PList.map_cons, ih_t]
      rw [map_app]; congr 1; exact map_comp (sublists as)
    simp only [sublists, eq_goal]
    apply nodup_append
    · exact ih_nodup
    · exact nodup_map_cons_a a as ha_nd (sublists as) (fun ws hw => hw) ih_nodup
    · intro x hx y hy
      obtain ⟨ws, hws, rfl⟩ := (PList.Mem_map CList.mk x (sublists as)).mp hx
      obtain ⟨vs, hvs, rfl⟩ :=
        (PList.Mem_map (fun ws => CList.mk (PList.cons a ws)) y (sublists as)).mp hy
      have ha_not_ws := a_not_mem_sublist a as ha_nd ws hws
      change CList.extEq (CList.mk ws) (CList.mk (PList.cons a vs)) = false
      exact cross_not_extEq a ws vs ha_not_ws

theorem length_sublists {α : Type} (xs : PList α) :
    PList.length (sublists xs) = pow 𝟚 (PList.length xs) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sublists, PList.length_cons]
    show PList.length ((sublists as).append ((sublists as).map (PList.cons a))) =
         pow 𝟚 (σ (PList.length as))
    rw [PList.length_append, PList.length_map]
    simp only [ih]
    rw [← mul_two, ← pow_succ]

end CList

namespace HFSet

def powersetCList (A : CList) : CList :=
  match A with
  | CList.mk xs => CList.mk ((CList.sublists xs).map CList.mk)

/-- Caracterización fundamental de la pertenencia al powerset a nivel CList:
    `y ∈ powerset(A) ↔ y ⊆ A`. -/
theorem mem_powersetCList
    (y A : CList) :
    CList.mem y (powersetCList A) = true ↔ CList.subset y A = true := by
  match A with
  | CList.mk xs =>
    constructor
    · intro h
      simp only [powersetCList, CList.mem_eq_any, PList.any_eq_true, PList.Mem_map] at h
      obtain ⟨w, ⟨zs, hzs, rfl⟩, hyw⟩ := h
      have h_sub_zs : CList.subset (CList.mk zs) (CList.mk xs) = true :=
        CList.sublists_subset xs zs hzs
      have h_sub_y : CList.subset y (CList.mk zs) = true := by
        rw [CList.extEq_def, Bool.and_eq_true] at hyw; exact hyw.1
      exact CList.subset_trans y (CList.mk zs) (CList.mk xs) h_sub_y h_sub_zs
    · intro h
      let P := fun z => CList.mem z y
      have hP_resp : CList.P_respects P := CList.mem_right_respects_extEq y
      have h_filtered : PList.Mem (PList.filter P xs) (CList.sublists xs) :=
        CList.filter_in_sublists P xs
      have h_sub1 : CList.subset y (CList.mk (PList.filter P xs)) = true := by
        rw [subset_iff_forall_mem_clist]
        intro w hw
        have hw_xs : CList.mem w (CList.mk xs) = true :=
          CList.mem_subset w y (CList.mk xs) hw h
        exact CList.mem_filter_of_mem P hP_resp w xs hw_xs hw
      have h_sub2 : CList.subset (CList.mk (PList.filter P xs)) y = true := by
        rw [subset_iff_forall_mem_clist]
        intro w hw
        exact CList.P_of_mem_filter P hP_resp w xs hw
      have h_extEq : CList.extEq y (CList.mk (PList.filter P xs)) = true := by
        rw [CList.extEq_def, Bool.and_eq_true]; exact ⟨h_sub1, h_sub2⟩
      simp only [powersetCList, CList.mem_eq_any, PList.any_eq_true, PList.Mem_map]
      exact ⟨CList.mk (PList.filter P xs),
             ⟨PList.filter P xs, h_filtered, rfl⟩,
             h_extEq⟩

theorem powersetCList_extEq
    (A₁ A₂ : CList) (h : CList.extEq A₁ A₂ = true) :
    CList.extEq (powersetCList A₁) (powersetCList A₂) = true := by
  rw [CList.extEq_def, Bool.and_eq_true]
  have h12 : CList.subset A₁ A₂ = true := by
    rw [CList.extEq_def, Bool.and_eq_true] at h; exact h.1
  have h21 : CList.subset A₂ A₁ = true := by
    rw [CList.extEq_def, Bool.and_eq_true] at h; exact h.2
  constructor
  · rw [subset_iff_forall_mem_clist]
    intro y hy
    rw [mem_powersetCList] at hy ⊢
    exact CList.subset_trans y A₁ A₂ hy h12
  · rw [subset_iff_forall_mem_clist]
    intro y hy
    rw [mem_powersetCList] at hy ⊢
    exact CList.subset_trans y A₂ A₁ hy h21

def powerset (A : HFSet) : HFSet :=
  Quotient.liftOn A
    (fun a => Quotient.mk CList.Setoid (powersetCList a))
    (fun a₁ a₂ ha => by
      apply Quotient.sound
      exact powersetCList_extEq a₁ a₂ ha)

end HFSet
