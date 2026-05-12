/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.HFSets

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
