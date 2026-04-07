import AczelSetTheory.CList.Order
import AczelSetTheory.CList.SetEquiv

-- ==========================================
-- Sorted, propiedades de ordenación y dedup
-- ==========================================

namespace CList

def Sorted : List CList → Prop
  | []           => True
  | [_]          => True
  | a :: b :: rest => lt a b = true ∧ Sorted (b :: rest)

private theorem orderedInsert_sorted
  (x : CList) (l : List CList) (hs : Sorted l) :
    Sorted (orderedInsert x l)
      := by
  induction l with
  | nil => simp [orderedInsert, Sorted]
  | cons y ys ih =>
    simp only [orderedInsert]
    by_cases hxy : lt x y = true
    · rw [if_pos hxy]
      match ys with
      | []     => simp [Sorted, hxy]
      | z :: _ => exact ⟨hxy, hs⟩
    · rw [if_neg hxy]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]; exact hs
      · rw [if_neg heq]
        have hyx : lt y x = true := by
          rcases lt_total_extEq x y (by simp [heq]) with h | h
          · exact absurd h (by simp [hxy])
          · exact h
        match ys with
        | [] => simp [orderedInsert, Sorted, hyx]
        | z :: rest =>
          obtain ⟨hyz, hs_rest⟩ := hs
          specialize ih hs_rest
          -- ih : Sorted (orderedInsert x (z :: rest))
          -- goal : Sorted (y :: orderedInsert x (z :: rest))
          by_cases hxz : lt x z = true
          · have hins : orderedInsert x (z :: rest) = x :: z :: rest := by
              unfold orderedInsert; rw [if_pos hxz]
            rw [hins] at ih ⊢
            exact ⟨hyx, hxz, hs_rest⟩
          · by_cases heqz : extEq x z = true
            · have hins : orderedInsert x (z :: rest) = z :: rest := by
                unfold orderedInsert; rw [if_neg hxz, if_pos heqz]
              rw [hins] at ih ⊢
              exact ⟨hyz, hs_rest⟩
            · have hins : orderedInsert x (z :: rest) = z :: orderedInsert x rest := by
                simp only [orderedInsert, if_neg hxz, if_neg heqz]
              rw [hins] at ih ⊢
              exact ⟨hyz, ih⟩

theorem insertionSort_sorted
  (l : List CList) :
    Sorted (insertionSort l)
      := by
  induction l with
  | nil => simp [insertionSort, Sorted]
  | cons x xs ih => exact orderedInsert_sorted x (insertionSort xs) ih

-- Elementos de (orderedInsert x l) son un subconjunto de {x} ∪ l
private theorem mem_of_mem_orderedInsert
  (x z : CList) (l : List CList) :
    z ∈ orderedInsert x l → z = x ∨ z ∈ l
      := by
  induction l with
  | nil =>
    simp [orderedInsert]
  | cons y ys ih =>
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
      intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]
        intro hmem; exact Or.inr hmem
      · rw [if_neg heq]
        intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · rcases ih h with rfl | h'
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

-- Elementos de (insertionSort l) son elementos de l
theorem insertionSort_mem_subset
  (z : CList) (l : List CList) :
    z ∈ insertionSort l → z ∈ l
      := by
  induction l with
  | nil => simp [insertionSort]
  | cons y ys ih =>
    simp only [insertionSort]
    intro hmem
    rcases mem_of_mem_orderedInsert y z (insertionSort ys) hmem with rfl | h
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (ih h))

private theorem orderedInsert_nodup
  (x : CList) (l : List CList)
  (hxl : ∀ y ∈ l, extEq x y = false)
  (hl : Nodup l) :
    Nodup (orderedInsert x l)
      := by
  induction l with
  | nil => simp [orderedInsert, Nodup]
  | cons y ys ih =>
    have hxy : extEq x y = false := hxl y (List.mem_cons.mpr (Or.inl rfl))
    have hxys : ∀ w ∈ ys, extEq x w = false :=
      fun w hw => hxl w (List.mem_cons.mpr (Or.inr hw))
    simp only [Nodup, List.pairwise_cons] at hl
    obtain ⟨hyl, hys⟩ := hl
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
      simp only [Nodup, List.pairwise_cons]
      refine ⟨fun b hb => ?_, hyl, hys⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hxy
      · exact hxys b hb
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · exact absurd heq (by simp [hxy])
      · rw [if_neg heq]
        simp only [Nodup, List.pairwise_cons]
        refine ⟨fun z hz => ?_, ih hxys hys⟩
        rcases mem_of_mem_orderedInsert x z ys hz with rfl | h
        · rw [extEq_comm]; exact hxy
        · exact hyl z h

theorem insertionSort_nodup
  (l : List CList) (hl : Nodup l) :
    Nodup (insertionSort l)
      := by
  induction l with
  | nil => simp [insertionSort, Nodup]
  | cons x xs ih =>
    simp only [Nodup, List.pairwise_cons] at hl
    obtain ⟨hx, hxs⟩ := hl
    simp only [insertionSort]
    apply orderedInsert_nodup
    · intro y hy
      exact hx y (insertionSort_mem_subset y xs hy)
    · exact ih hxs

/-- orderedInsert conserva la equivalencia de conjuntos (modulo extEq-dedup). -/
private theorem orderedInsert_setEquiv
  (x : CList) (l : List CList) :
    SetEquiv (orderedInsert x l) (x :: l)
      := by
  induction l with
  | nil => simp [orderedInsert]; exact SetEquiv.refl _
  | cons y ys ih =>
    intro z
    simp only [orderedInsert]
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]
        simp only [List.any_cons, Bool.or_eq_true]
        constructor
        · rintro (hzy | hys)
          · exact Or.inr (Or.inl hzy)
          · exact Or.inr (Or.inr hys)
        · rintro (hzx | hzy | hys)
          · exact Or.inl (extEq_trans z x y hzx heq)
          · exact Or.inl hzy
          · exact Or.inr hys
      · rw [if_neg heq]
        simp only [List.any_cons, Bool.or_eq_true]
        have ih_z := ih z
        simp only [List.any_cons, Bool.or_eq_true] at ih_z
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

/-- insertionSort conserva la equivalencia de conjuntos. -/
theorem insertionSort_setEquiv
  (l : List CList) :
    SetEquiv (insertionSort l) l
      := by
  induction l with
  | nil => exact SetEquiv.refl []
  | cons x xs ih =>
    intro z
    have h1 := orderedInsert_setEquiv x (insertionSort xs)
    simp only [insertionSort]
    constructor
    · intro hz
      have := (h1 z).mp hz
      simp only [List.any_cons, Bool.or_eq_true] at this ⊢
      rcases this with hzx | hzs
      · exact Or.inl hzx
      · exact Or.inr ((ih z).mp hzs)
    · intro hz
      simp only [List.any_cons, Bool.or_eq_true] at hz
      apply (h1 z).mpr
      simp only [List.any_cons, Bool.or_eq_true]
      rcases hz with hzx | hzxs
      · exact Or.inl hzx
      · exact Or.inr ((ih z).mpr hzxs)

end CList
