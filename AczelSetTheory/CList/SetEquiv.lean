/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.CList.ExtEq

-- ==========================================
-- SetEquiv: Nodup, equivalencia de conjuntos
-- ==========================================

namespace CList

-- ─────────────────────────────────────────────────────────────────
-- Nodup
-- ─────────────────────────────────────────────────────────────────

def Nodup : PList CList → Prop
  | .nil      => True
  | .cons x xs => (∀ y ∈ xs, extEq x y = false) ∧ Nodup xs

theorem dedup_nodup (l : PList CList) : Nodup (dedup l) := by
  have stronger_lemma : ∀ (l' : PList CList) (vistos : PList CList),
      Nodup (dedupAux l' vistos) ∧
      (∀ y, PList.Mem y (dedupAux l' vistos) →
            PList.any (fun z => extEq y z) vistos = false) := by
    intro l'
    induction l' with
    | nil =>
      intro _; exact ⟨trivial, fun y h => absurd h (PList.not_mem_nil _)⟩
    | cons head tail IH =>
      intro vistos
      simp only [dedupAux]
      by_cases h_seen : PList.any (fun y => extEq head y) vistos = true
      · rw [if_pos h_seen]; exact IH vistos
      · rw [if_neg h_seen]
        have h_false : PList.any (fun y => extEq head y) vistos = false :=
          Bool.eq_false_iff.mpr (fun h => h_seen h)
        rcases IH (.cons head vistos) with ⟨nodup_tail, tail_is_new⟩
        constructor
        · simp only [Nodup]
          constructor
          · intro y y_in_tail
            have hn := tail_is_new y y_in_tail
            rw [PList.any_cons, Bool.or_eq_false_iff] at hn
            rw [extEq_comm]; exact hn.1
          · exact nodup_tail
        · intro y y_in_list
          cases y_in_list with
          | head => exact h_false
          | tail h_y_in_tail =>
            have hn := tail_is_new y h_y_in_tail
            rw [PList.any_cons, Bool.or_eq_false_iff] at hn
            exact hn.2
  rw [dedup]
  exact (stronger_lemma l .nil).1

-- ─────────────────────────────────────────────────────────────────
-- SetEquiv
-- ─────────────────────────────────────────────────────────────────

def SetEquiv (l₁ l₂ : PList CList) : Prop :=
  ∀ x, (PList.any (fun y => extEq x y) l₁ = true) ↔
       (PList.any (fun y => extEq x y) l₂ = true)

namespace SetEquiv

@[refl]
theorem refl (l : PList CList) : SetEquiv l l := fun _ => Iff.rfl

@[symm]
theorem symm {l₁ l₂ : PList CList} (h : SetEquiv l₁ l₂) : SetEquiv l₂ l₁ :=
  fun x => (h x).symm

theorem trans {l₁ l₂ l₃ : PList CList}
    (h₁₂ : SetEquiv l₁ l₂) (h₂₃ : SetEquiv l₂ l₃) : SetEquiv l₁ l₃ :=
  fun x => (h₁₂ x).trans (h₂₃ x)

end SetEquiv

theorem mem_eq_any (x : CList) (l : PList CList) :
    mem x (mk l) = PList.any (fun y => extEq x y) l := by
  induction l with
  | nil => simp [mem_nil, PList.any]
  | cons y ys ih => simp [mem_cons, ih, PList.any]

private theorem subset_iff_forall_mem
    (l₁ l₂ : PList CList) :
    subset (mk l₁) (mk l₂) = true ↔ (∀ x ∈ l₁, mem x (mk l₂) = true) := by
  induction l₁ with
  | nil =>
    constructor
    · intro _ x hx; exact absurd hx (PList.not_mem_nil _)
    · intro _; exact subset_nil _
  | cons x xs ih =>
    simp only [subset_cons, Bool.and_eq_true]
    constructor
    · intro ⟨h1, h2⟩ y hy
      cases hy with
      | head => exact h1
      | tail hys => exact ih.mp h2 y hys
    · intro h
      exact ⟨h x PList.Mem.head, ih.mpr (fun y hy => h y (PList.Mem.tail hy))⟩

theorem extEq_mk_iff_setEquiv
    (l₁ l₂ : PList CList) :
    extEq (mk l₁) (mk l₂) = true ↔ SetEquiv l₁ l₂ := by
  constructor
  · intro h
    unfold SetEquiv
    rw [extEq_def, Bool.and_eq_true] at h
    simp only [subset_iff_forall_mem, mem_eq_any] at h
    obtain ⟨h1, h2⟩ := h
    intro x
    constructor
    · intro hx
      obtain ⟨z, hz, hxz⟩ := (PList.any_eq_true _ _).mp hx
      obtain ⟨w, hw, hzw⟩ := (PList.any_eq_true _ _).mp (h1 z hz)
      exact (PList.any_eq_true _ _).mpr ⟨w, hw, extEq_trans x z w hxz hzw⟩
    · intro hx
      obtain ⟨z, hz, hxz⟩ := (PList.any_eq_true _ _).mp hx
      obtain ⟨w, hw, hzw⟩ := (PList.any_eq_true _ _).mp (h2 z hz)
      exact (PList.any_eq_true _ _).mpr ⟨w, hw, extEq_trans x z w hxz hzw⟩
  · intro h
    unfold SetEquiv at h
    rw [extEq_def, Bool.and_eq_true]
    simp only [subset_iff_forall_mem, mem_eq_any]
    exact ⟨fun x hx => (h x).mp  ((PList.any_eq_true _ _).mpr ⟨x, hx, extEq_refl x⟩),
           fun x hx => (h x).mpr ((PList.any_eq_true _ _).mpr ⟨x, hx, extEq_refl x⟩)⟩

theorem dedup_setEquiv_self (l : PList CList) : SetEquiv (dedup l) l := by
  intro x; constructor
  · intro h_mem_reduced
    obtain ⟨z, z_in_reduced, xz_eq⟩ := (PList.any_eq_true _ _).mp h_mem_reduced
    have z_in_l_ext : PList.any (fun y => extEq z y) l = true := by
      have helper : ∀ (l' vistos : PList CList), ∀ z', PList.Mem z' (dedupAux l' vistos) →
          PList.any (fun y => extEq z' y) l' = true ∨
          PList.any (fun y => extEq z' y) vistos = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h; exact absurd h (PList.not_mem_nil _)
        | cons head tail IH =>
          intro vistos z' h_mem
          unfold dedupAux at h_mem
          by_cases h_seen : PList.any (fun y => extEq head y) vistos = true
          · rw [if_pos h_seen] at h_mem
            rcases IH vistos z' h_mem with (h | h)
            · exact Or.inl (by rw [PList.any_cons]; simp [h])
            · exact Or.inr h
          · rw [if_neg h_seen] at h_mem
            cases h_mem with
            | head =>
              exact Or.inl (by rw [PList.any_cons]; simp [extEq_refl])
            | tail h_in_tail =>
              rcases IH (.cons head vistos) z' h_in_tail with (h_in_t | h_in_v)
              · exact Or.inl (by rw [PList.any_cons]; simp [h_in_t])
              · rw [PList.any_cons, Bool.or_eq_true] at h_in_v
                rcases h_in_v with (h_head | h_vis)
                · exact Or.inl (by rw [PList.any_cons]; simp [h_head])
                · exact Or.inr h_vis
      rw [dedup] at z_in_reduced
      rcases helper l .nil z z_in_reduced with (h | h)
      · exact h
      · simp [PList.any] at h
    obtain ⟨w, w_in_l, zw_eq⟩ := (PList.any_eq_true _ _).mp z_in_l_ext
    exact (PList.any_eq_true _ _).mpr ⟨w, w_in_l, CList.extEq_trans x z w xz_eq zw_eq⟩
  · intro h_mem_l
    obtain ⟨z, z_in_l, xz_eq⟩ := (PList.any_eq_true _ _).mp h_mem_l
    have completeness_aux : ∀ z' ∈ l,
        PList.any (fun y => extEq z' y) (dedup l) = true := by
      have helper : ∀ (l' vistos : PList CList), ∀ z', PList.Mem z' l' →
          PList.any (fun y => extEq z' y) (dedupAux l' vistos) = true ∨
          PList.any (fun y => extEq z' y) vistos = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h; exact absurd h (PList.not_mem_nil _)
        | cons hd tail IH =>
          intro vistos z' h_mem
          cases h_mem with
          | head =>
            simp only [dedupAux]
            by_cases h_seen : PList.any (fun y => extEq hd y) vistos = true
            · rw [if_pos h_seen]; exact Or.inr h_seen
            · rw [if_neg h_seen]
              exact Or.inl (by rw [PList.any_cons]; simp [extEq_refl])
          | tail h_in_tail =>
            simp only [dedupAux]
            by_cases h_seen : PList.any (fun y => extEq hd y) vistos = true
            · rw [if_pos h_seen]; exact IH vistos z' h_in_tail
            · rw [if_neg h_seen]
              rcases IH (.cons hd vistos) z' h_in_tail with (h_in_res | h_in_v_ext)
              · exact Or.inl (by rw [PList.any_cons]; simp [h_in_res])
              · rw [PList.any_cons, Bool.or_eq_true] at h_in_v_ext
                rcases h_in_v_ext with (h_hd | h_vis)
                · exact Or.inl (by rw [PList.any_cons]; simp [h_hd])
                · exact Or.inr h_vis
      intro z' hz'
      rw [dedup]
      rcases helper l .nil z' hz' with (h | h)
      · exact h
      · simp [PList.any] at h
    have hz := completeness_aux z z_in_l
    obtain ⟨w, w_in_reduced, zw_eq⟩ := (PList.any_eq_true _ _).mp hz
    exact (PList.any_eq_true _ _).mpr ⟨w, w_in_reduced, CList.extEq_trans x z w xz_eq zw_eq⟩

private theorem extEq_cons_equiv
    (x y : CList) (xs ys : PList CList)
    (hxy : extEq x y = true) (hxsys : extEq (mk xs) (mk ys) = true) :
    extEq (mk (.cons x xs)) (mk (.cons y ys)) = true := by
  rw [extEq_mk_iff_setEquiv] at *
  intro z
  simp only [PList.any_cons, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl (extEq_trans z x y h hxy)
    · exact Or.inr ((hxsys z).mp h)
  · rintro (h | h)
    · have hyx : extEq y x = true := by rwa [extEq_comm] at hxy
      exact Or.inl (extEq_trans z y x h hyx)
    · exact Or.inr ((hxsys z).mpr h)

end CList
