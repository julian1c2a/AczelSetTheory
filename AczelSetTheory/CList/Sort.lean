/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.CList.Order
import AczelSetTheory.CList.SetEquiv

-- ==========================================
-- Sorted, propiedades de ordenación y dedup
-- ==========================================

namespace CList

def Sorted : PList CList → Prop
  | .nil                  => True
  | .cons _ .nil          => True
  | .cons a (.cons b rest) => lt a b = true ∧ Sorted (.cons b rest)

private theorem orderedInsert_sorted
    (x : CList) (l : PList CList) (hs : Sorted l) :
    Sorted (orderedInsert x l) := by
  induction l with
  | nil => simp [orderedInsert, Sorted]
  | cons y ys ih =>
    simp only [orderedInsert]
    by_cases hxy : lt x y = true
    · rw [if_pos hxy]
      match ys with
      | .nil      => simp [Sorted, hxy]
      | .cons z _ => exact ⟨hxy, hs⟩
    · rw [if_neg hxy]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]; exact hs
      · rw [if_neg heq]
        have hyx : lt y x = true := by
          rcases lt_total_extEq x y (by simp [heq]) with h | h
          · exact absurd h (by simp [hxy])
          · exact h
        match ys with
        | .nil => simp [orderedInsert, Sorted, hyx]
        | .cons z rest =>
          obtain ⟨hyz, hs_rest⟩ := hs
          specialize ih hs_rest
          by_cases hxz : lt x z = true
          · have hins : orderedInsert x (.cons z rest) = .cons x (.cons z rest) := by
              unfold orderedInsert; rw [if_pos hxz]
            rw [hins] at ih ⊢
            exact ⟨hyx, hxz, hs_rest⟩
          · by_cases heqz : extEq x z = true
            · have hins : orderedInsert x (.cons z rest) = .cons z rest := by
                unfold orderedInsert; rw [if_neg hxz, if_pos heqz]
              rw [hins] at ih ⊢
              exact ⟨hyz, hs_rest⟩
            · have hins : orderedInsert x (.cons z rest) = .cons z (orderedInsert x rest) := by
                simp only [orderedInsert, if_neg hxz, if_neg heqz]
              rw [hins] at ih ⊢
              exact ⟨hyz, ih⟩

theorem insertionSort_sorted (l : PList CList) : Sorted (insertionSort l) := by
  induction l with
  | nil => simp [insertionSort, Sorted]
  | cons x xs ih => exact orderedInsert_sorted x (insertionSort xs) ih

private theorem mem_of_mem_orderedInsert
    (x z : CList) (l : PList CList) :
    PList.Mem z (orderedInsert x l) → z = x ∨ PList.Mem z l := by
  induction l with
  | nil =>
    simp only [orderedInsert]
    intro h
    cases h with
    | head => exact Or.inl rfl
    | tail h' => exact absurd h' (PList.not_mem_nil _)
  | cons y ys ih =>
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
      intro hmem
      cases hmem with
      | head => exact Or.inl rfl
      | tail h =>
        cases h with
        | head => exact Or.inr PList.Mem.head
        | tail h' => exact Or.inr (PList.Mem.tail h')
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]
        intro hmem; exact Or.inr hmem
      · rw [if_neg heq]
        intro hmem
        cases hmem with
        | head => exact Or.inr PList.Mem.head
        | tail h =>
          rcases ih h with rfl | h'
          · exact Or.inl rfl
          · exact Or.inr (PList.Mem.tail h')

theorem insertionSort_mem_subset
    (z : CList) (l : PList CList) :
    PList.Mem z (insertionSort l) → PList.Mem z l := by
  induction l with
  | nil => simp [insertionSort]
  | cons y ys ih =>
    simp only [insertionSort]
    intro hmem
    rcases mem_of_mem_orderedInsert y z (insertionSort ys) hmem with rfl | h
    · exact PList.Mem.head
    · exact PList.Mem.tail (ih h)

private theorem orderedInsert_nodup
    (x : CList) (l : PList CList)
    (hxl : ∀ y ∈ l, extEq x y = false)
    (hl : Nodup l) :
    Nodup (orderedInsert x l) := by
  induction l with
  | nil => exact ⟨fun y hy => absurd hy (PList.not_mem_nil _), trivial⟩
  | cons y ys ih =>
    have hxy : extEq x y = false := hxl y PList.Mem.head
    have hxys : ∀ w ∈ ys, extEq x w = false :=
      fun w hw => hxl w (PList.Mem.tail hw)
    obtain ⟨hyl, hys⟩ := hl
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
      simp only [Nodup]
      refine ⟨fun b hb => ?_, hyl, hys⟩
      cases hb with
      | head => exact hxy
      | tail hb' => exact hxys b hb'
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · exact absurd heq (by simp [hxy])
      · rw [if_neg heq]
        simp only [Nodup]
        refine ⟨fun z hz => ?_, ih hxys hys⟩
        rcases mem_of_mem_orderedInsert x z ys hz with rfl | h
        · rw [extEq_comm]; exact hxy
        · exact hyl z h

theorem insertionSort_nodup
    (l : PList CList) (hl : Nodup l) :
    Nodup (insertionSort l) := by
  induction l with
  | nil => simp [insertionSort, Nodup]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := hl
    simp only [insertionSort]
    apply orderedInsert_nodup
    · intro y hy
      exact hx y (insertionSort_mem_subset y xs hy)
    · exact ih hxs

private theorem orderedInsert_setEquiv
    (x : CList) (l : PList CList) :
    SetEquiv (orderedInsert x l) (.cons x l) := by
  induction l with
  | nil => exact SetEquiv.refl _
  | cons y ys ih =>
    intro z
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]
        simp only [PList.any_cons, Bool.or_eq_true]
        constructor
        · rintro (hzy | hys)
          · exact Or.inr (Or.inl hzy)
          · exact Or.inr (Or.inr hys)
        · rintro (hzx | hzy | hys)
          · exact Or.inl (extEq_trans z x y hzx heq)
          · exact Or.inl hzy
          · exact Or.inr hys
      · rw [if_neg heq]
        simp only [PList.any_cons, Bool.or_eq_true]
        have ih_z := ih z
        simp only [PList.any_cons, Bool.or_eq_true] at ih_z
        constructor
        · rintro (hzy | hrs)
          · exact Or.inr (Or.inl hzy)
          · rcases ih_z.mp hrs with hzx | hzys
            · exact Or.inl hzx
            · exact Or.inr (Or.inr hzys)
        · rintro (hzx | hzy | hys)
          · exact Or.inr (ih_z.mpr (Or.inl hzx))
          · exact Or.inl hzy
          · exact Or.inr (ih_z.mpr (Or.inr hys))

theorem insertionSort_setEquiv (l : PList CList) : SetEquiv (insertionSort l) l := by
  induction l with
  | nil => exact SetEquiv.refl _
  | cons x xs ih =>
    intro z
    have h1 := orderedInsert_setEquiv x (insertionSort xs)
    simp only [insertionSort]
    constructor
    · intro hz
      have := (h1 z).mp hz
      simp only [PList.any_cons, Bool.or_eq_true] at this ⊢
      rcases this with hzx | hzs
      · exact Or.inl hzx
      · exact Or.inr ((ih z).mp hzs)
    · intro hz
      simp only [PList.any_cons, Bool.or_eq_true] at hz
      apply (h1 z).mpr
      simp only [PList.any_cons, Bool.or_eq_true]
      rcases hz with hzx | hzxs
      · exact Or.inl hzx
      · exact Or.inr ((ih z).mpr hzxs)

theorem sorted_head_lt_of_mem {a b : CList} {l : PList CList}
    (hs : Sorted (.cons a l)) (hm : PList.Mem b l) : lt a b = true :=
  match l, hm with
  | .cons _ _,    .head      => hs.1
  | .cons c rest, .tail hrest =>
      lt_trans a c b hs.1 (sorted_head_lt_of_mem hs.2 hrest)
termination_by sizeOf l
decreasing_by simp_wf; simp [sizeOf]; omega

theorem length_orderedInsert_fresh (x : CList) (l : PList CList)
    (hx : ∀ y, PList.Mem y l → extEq x y = false) :
    PList.length (orderedInsert x l) = σ (PList.length l) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have hxy : extEq x y = false := hx y PList.Mem.head
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]; rfl
    · rw [if_neg hlt, if_neg (Bool.eq_false_iff.mp hxy)]
      simp only [PList.length_cons]
      congr 1
      exact ih (fun z hz => hx z (PList.Mem.tail hz))

theorem length_insertionSort_nodup (l : PList CList) (hn : Nodup l) :
    PList.length (insertionSort l) = PList.length l := by
  induction l with
  | nil => simp [insertionSort]
  | cons x xs ih =>
    obtain ⟨hx_nd, hxs_nd⟩ := hn
    simp only [insertionSort, PList.length_cons]
    rw [length_orderedInsert_fresh x (insertionSort xs), ih hxs_nd]
    intro y hy
    exact hx_nd y (insertionSort_mem_subset y xs hy)

end CList
