/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.CList.ExtEq

namespace CList

-- P will respect ExtEq
def P_respects (P : CList → Bool) : Prop :=
  ∀ (x y : CList), extEq x y = true → P x = P y

theorem subset_filter
    (P : CList → Bool) (xs : PList CList) :
    subset (mk (PList.filter P xs)) (mk xs) = true := by
  induction xs with
  | nil => exact subset_nil _
  | cons z zs ih =>
    simp only [PList.filter]
    split
    · simp only [subset_cons, Bool.and_eq_true]
      exact ⟨by simp only [mem_cons, extEq_refl, Bool.true_or], subset_mono (PList.filter P zs) z zs ih⟩
    · exact subset_mono (PList.filter P zs) z zs ih

theorem mem_filter_of_mem
    (P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : PList CList)
    (hx : mem x (mk xs) = true) (hPx : P x = true) :
    mem x (mk (PList.filter P xs)) = true := by
  induction xs with
  | nil => simp [mem_nil] at hx
  | cons z zs ih =>
    simp only [PList.filter]
    simp only [mem_cons, Bool.or_eq_true] at hx
    cases hx with
    | inl heq =>
      have hzP : P z = true := by
        have : P z = P x := hP_resp z x (extEq_comm x z ▸ heq)
        rw [this]; exact hPx
      simp only [hzP, ite_true, mem_cons, Bool.or_eq_true]
      exact Or.inl heq
    | inr hmem =>
      have hind := ih hmem
      split
      · simp only [mem_cons, Bool.or_eq_true]
        exact Or.inr hind
      · exact hind

theorem filter_subset_filter
    (P : CList → Bool) (hP_resp : P_respects P) (xs ys : PList CList)
    (hsub : subset (mk xs) (mk ys) = true) :
    subset (mk (PList.filter P xs)) (mk (PList.filter P ys)) = true := by
  induction xs with
  | nil => exact subset_nil _
  | cons z zs ih =>
    simp only [PList.filter]
    split
    · next hzP =>
      simp only [subset_cons, Bool.and_eq_true]
      have hz_in_xs : mem z (mk (.cons z zs)) = true := by
        simp only [mem_cons, extEq_refl, Bool.true_or]
      have hz_in_ys : mem z (mk ys) = true :=
        mem_subset z (mk (.cons z zs)) (mk ys) hz_in_xs hsub
      have hz_in_ys_filter : mem z (mk (PList.filter P ys)) = true :=
        mem_filter_of_mem P hP_resp z ys hz_in_ys hzP
      have hzs_sub_ys : subset (mk zs) (mk ys) = true := by
        simp only [subset_cons, Bool.and_eq_true] at hsub
        exact hsub.2
      exact ⟨hz_in_ys_filter, ih hzs_sub_ys⟩
    · simp only [subset_cons, Bool.and_eq_true] at hsub
      exact ih hsub.2

theorem extEq_filter
    (P : CList → Bool) (hP_resp : P_respects P) (xs ys : PList CList)
    (heq : extEq (mk xs) (mk ys) = true) :
    extEq (mk (PList.filter P xs)) (mk (PList.filter P ys)) = true := by
  simp only [extEq_def, Bool.and_eq_true] at heq ⊢
  exact ⟨filter_subset_filter P hP_resp xs ys heq.1,
         filter_subset_filter P hP_resp ys xs heq.2⟩

theorem P_of_mem_filter
    (P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : PList CList)
    (hx : mem x (mk (PList.filter P xs)) = true) :
    P x = true := by
  induction xs with
  | nil => simp [PList.filter, mem_nil] at hx
  | cons z zs ih =>
    simp only [PList.filter] at hx
    split at hx
    · next hzP =>
      simp only [mem_cons, Bool.or_eq_true] at hx
      cases hx with
      | inl heq =>
        have h_px_pz : P x = P z := hP_resp x z heq
        rw [h_px_pz]; exact hzP
      | inr hmem => exact ih hmem
    · exact ih hx

end CList
