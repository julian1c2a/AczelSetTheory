import AczelSetTheory.CList.ExtEq

-- ==========================================
-- SetEquiv: Nodup, equivalencia de conjuntos
-- ==========================================

namespace CList

/--
Define la propiedad de que una lista no tiene duplicados según `extEq`.
-/
def Nodup (l : List CList) : Prop :=
  l.Pairwise (fun a b => extEq a b = false)

-- Lema: dedup produce una lista sin duplicados.
theorem dedup_nodup
  (l : List CList) :
    Nodup (dedup l)
      := by
  have stronger_lemma : ∀ (l' : List CList) (vistos : List CList),
    Nodup (dedupAux l' vistos) ∧
    (∀ y ∈ (dedupAux l' vistos), (vistos.any (fun z => extEq y z)) = false) := by
    intro l'
    induction l' with
    | nil =>
      intro _; simp [dedupAux, Nodup]
    | cons head tail IH =>
      intro vistos
      simp only [dedupAux]
      by_cases h_seen : (vistos.any fun y => extEq head y) = true
      · rw [if_pos h_seen]; exact IH vistos
      · rw [if_neg h_seen]
        have h_false : (vistos.any fun y => extEq head y) = false :=
          Bool.eq_false_iff.mpr (fun h => h_seen h)
        have ih_recursed := IH (head :: vistos)
        rcases ih_recursed with ⟨nodup_tail, tail_is_new⟩
        constructor
        · simp only [Nodup, List.pairwise_cons]
          constructor
          · have extEq_comm : ∀ a b, extEq a b = extEq b a := by
              intros a b; simp [extEq, evalOp, Bool.and_comm]
            intro y y_in_tail
            specialize tail_is_new y y_in_tail
            rw [List.any_cons, Bool.or_eq_false_iff] at tail_is_new
            rw [extEq_comm]; exact tail_is_new.1
          · exact nodup_tail
        · intro y y_in_list
          simp only [List.mem_cons] at y_in_list
          cases y_in_list with
          | inl h_y_eq_head =>
            rw [h_y_eq_head]; exact h_false
          | inr h_y_in_tail =>
            specialize tail_is_new y h_y_in_tail
            rw [List.any_cons, Bool.or_eq_false_iff] at tail_is_new
            exact tail_is_new.2
  rw [dedup]
  exact (stronger_lemma l []).1

/--
Define la equivalencia de conjuntos entre dos listas.
-/
def SetEquiv (l₁ l₂ : List CList) : Prop :=
  ∀ x, (l₁.any (fun y => extEq x y)) ↔ (l₂.any (fun y => extEq x y))

namespace SetEquiv

@[refl]
theorem refl
  (l : List CList) :
    SetEquiv l l
      := by
  intro _; exact Iff.rfl

@[symm]
theorem symm {l₁ l₂ : List CList}
  (h : SetEquiv l₁ l₂) :
    SetEquiv l₂ l₁
      := by
  intro x; exact (h x).symm

theorem trans {l₁ l₂ l₃ : List CList}
  (h₁₂ : SetEquiv l₁ l₂) (h₂₃ : SetEquiv l₂ l₃) :
    SetEquiv l₁ l₃
      := by
  intro x; exact (h₁₂ x).trans (h₂₃ x)

end SetEquiv

theorem mem_eq_any
  (x : CList) (l : List CList) :
    mem x (mk l) = l.any (fun y => extEq x y)
      := by
  induction l with
  | nil => simp [mem_nil]
  | cons y ys ih => simp [mem_cons, ih]

private theorem subset_iff_forall_mem
  (l₁ l₂ : List CList) :
    subset (mk l₁) (mk l₂) = true ↔ (∀ x ∈ l₁, mem x (mk l₂) = true)
      := by
  induction l₁ with
  | nil => simp [subset_nil]
  | cons x xs ih =>
    simp only [subset_cons, Bool.and_eq_true]
    constructor
    · intro ⟨h1, h2⟩ y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h1
      · exact ih.mp h2 y hy
    · intro h
      exact ⟨h x List.mem_cons_self, ih.mpr (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem extEq_mk_iff_setEquiv
  (l₁ l₂ : List CList) :
    extEq (mk l₁) (mk l₂) = true ↔ SetEquiv l₁ l₂
      := by
  constructor
  · intro h
    unfold SetEquiv
    rw [extEq_def, Bool.and_eq_true] at h
    simp only [subset_iff_forall_mem, mem_eq_any] at h
    obtain ⟨h1, h2⟩ := h
    intro x
    constructor
    · intro hx
      rw [List.any_eq_true] at hx
      obtain ⟨z, hz, hxz⟩ := hx
      have hzl2 := h1 z hz
      rw [List.any_eq_true] at hzl2
      obtain ⟨w, hw, hzw⟩ := hzl2
      exact List.any_eq_true.mpr ⟨w, hw, extEq_trans x z w hxz hzw⟩
    · intro hx
      rw [List.any_eq_true] at hx
      obtain ⟨z, hz, hxz⟩ := hx
      have hzl1 := h2 z hz
      rw [List.any_eq_true] at hzl1
      obtain ⟨w, hw, hzw⟩ := hzl1
      exact List.any_eq_true.mpr ⟨w, hw, extEq_trans x z w hxz hzw⟩
  · intro h
    unfold SetEquiv at h
    rw [extEq_def, Bool.and_eq_true]
    simp only [subset_iff_forall_mem, mem_eq_any]
    exact ⟨fun x hx => (h x).mp  (List.any_eq_true.mpr ⟨x, hx, extEq_refl x⟩),
           fun x hx => (h x).mpr (List.any_eq_true.mpr ⟨x, hx, extEq_refl x⟩)⟩

-- Lema: `dedup` conserva el conjunto de elementos.
theorem dedup_setEquiv_self
  (l : List CList) :
    SetEquiv (dedup l) l
      := by
  intro x; constructor
  · intro h_mem_reduced
    rw [List.any_eq_true] at h_mem_reduced
    obtain ⟨z, z_in_reduced, xz_eq⟩ := h_mem_reduced
    have z_in_l_ext : (l.any (fun y => extEq z y)) = true := by
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ (dedupAux l' vistos),
          (l'.any (fun y => extEq z' y)) = true ∨ (vistos.any (fun y => extEq z' y)) = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | cons head tail IH =>
          intro vistos z' h_mem
          unfold dedupAux at h_mem
          by_cases h_seen : (vistos.any (fun y => extEq head y)) = true
          · rw [if_pos h_seen] at h_mem
            rcases IH vistos z' h_mem with (h | h)
            · exact Or.inl (by simp [List.any_cons, h])
            · exact Or.inr h
          · rw [if_neg h_seen] at h_mem
            simp only [List.mem_cons] at h_mem
            rcases h_mem with (rfl | h_in_tail)
            · exact Or.inl (by simp [List.any_cons, extEq_refl])
            · rcases IH (head :: vistos) z' h_in_tail with (h_in_t | h_in_v)
              · exact Or.inl (by simp [List.any_cons, h_in_t])
              · rw [List.any_cons, Bool.or_eq_true] at h_in_v
                rcases h_in_v with (h_head | h_vis)
                · exact Or.inl (by simp [List.any_cons, h_head])
                · exact Or.inr h_vis
      rw [dedup] at z_in_reduced
      rcases helper l [] z z_in_reduced with (h | h)
      · exact h
      · simp at h
    rw [List.any_eq_true] at z_in_l_ext
    obtain ⟨w, w_in_l, zw_eq⟩ := z_in_l_ext
    exact List.any_eq_true.mpr ⟨w, w_in_l, CList.extEq_trans x z w xz_eq zw_eq⟩
  · intro h_mem_l
    rw [List.any_eq_true] at h_mem_l
    obtain ⟨z, z_in_l, xz_eq⟩ := h_mem_l
    have completeness_aux : ∀ z' ∈ l, (dedup l).any (fun y => extEq z' y) = true := by
      have helper : ∀ (l' vistos : List CList), ∀ z' ∈ l',
          (dedupAux l' vistos).any (fun y => extEq z' y) = true ∨
          (vistos.any (fun y => extEq z' y)) = true := by
        intro l'
        induction l' with
        | nil => intro vistos z' h_mem; cases h_mem
        | cons hd tail IH =>
          intro vistos z' h_mem
          simp only [dedupAux]
          rcases List.mem_cons.mp h_mem with (rfl | h_in_tail)
          · by_cases h_seen : (vistos.any (fun y => extEq z' y)) = true
            · rw [if_pos h_seen]; exact Or.inr h_seen
            · rw [if_neg h_seen]
              exact Or.inl (List.any_eq_true.mpr ⟨z', List.mem_cons_self, extEq_refl _⟩)
          · by_cases h_seen : (vistos.any (fun y => extEq hd y)) = true
            · rw [if_pos h_seen]; exact IH vistos z' h_in_tail
            · rw [if_neg h_seen]
              rcases IH (hd :: vistos) z' h_in_tail with (h_in_res | h_in_v_ext)
              · rw [List.any_eq_true] at h_in_res
                obtain ⟨w, hw, hwz⟩ := h_in_res
                exact Or.inl (List.any_eq_true.mpr ⟨w, List.mem_cons_of_mem hd hw, hwz⟩)
              · rw [List.any_cons, Bool.or_eq_true] at h_in_v_ext
                rcases h_in_v_ext with (h_hd | h_vis)
                · exact Or.inl (by simp [List.any_cons, h_hd])
                · exact Or.inr h_vis
      intro z' hz'
      rw [dedup]
      rcases helper l [] z' hz' with (h | h)
      · exact h
      · simp at h
    have hz := completeness_aux z z_in_l
    rw [List.any_eq_true] at hz
    obtain ⟨w, w_in_reduced, zw_eq⟩ := hz
    exact List.any_eq_true.mpr ⟨w, w_in_reduced, CList.extEq_trans x z w xz_eq zw_eq⟩

private theorem extEq_cons_equiv
  (x y : CList) (xs ys : List CList)
  (hxy : extEq x y = true) (hxsys : extEq (mk xs) (mk ys) = true) :
    extEq (mk (x :: xs)) (mk (y :: ys)) = true
      := by
  rw [extEq_mk_iff_setEquiv] at *
  intro z
  simp only [List.any_cons, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl (extEq_trans z x y h hxy)
    · exact Or.inr ((hxsys z).mp h)
  · rintro (h | h)
    · have hyx : extEq y x = true := by rwa [extEq_comm] at hxy
      exact Or.inl (extEq_trans z y x h hyx)
    · exact Or.inr ((hxsys z).mpr h)

end CList
