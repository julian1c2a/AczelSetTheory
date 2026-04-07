import AczelSetTheory.CList.Normalize

open CList

theorem extEq_normalize (A : CList) : extEq A (normalize A) = true := by
  match A with
  | mk xs =>
    simp only [normalize]
    rw [extEq_mk_iff_setEquiv]
    have ih_all : ∀ w ∈ xs, extEq w (normalize w) = true := fun w hw =>
      have : cSize w < cSize (mk xs) := cSize_lt_of_mem hw
      extEq_normalize w
    apply SetEquiv.trans (l₂ := xs.map normalize)
    · intro z
      constructor
      · intro hz
        obtain ⟨w, hw_mem, hw_eq⟩ := List.any_eq_true.mp hz
        apply List.any_eq_true.mpr
        have hw_ih : extEq w (normalize w) = true := ih_all w hw_mem
        exact ⟨normalize w, List.mem_map.mpr ⟨w, hw_mem, rfl⟩, extEq_trans z w (normalize w) hw_eq hw_ih⟩
      · intro hz
        obtain ⟨w_norm, hw_norm_mem, hw_norm_eq⟩ := List.any_eq_true.mp hz
        obtain ⟨w, hw_mem, rfl⟩ := List.mem_map.mp hw_norm_mem
        apply List.any_eq_true.mpr
        have hw_ih : extEq (normalize w) w = true := by rw [extEq_comm]; exact ih_all w hw_mem
        exact ⟨w, hw_mem, extEq_trans z (normalize w) w hw_norm_eq hw_ih⟩
    · apply SetEquiv.trans (l₂ := dedup (xs.map normalize))
      · exact SetEquiv.symm (dedup_setEquiv_self _)
      · exact SetEquiv.symm (insertionSort_setEquiv _)
termination_by cSize A

theorem extEq_iff_normalize_eq {A B : CList} : extEq A B = true ↔ normalize A = normalize B := by
  constructor
  · exact normalize_eq_of_extEq
  · intro h
    have ha : extEq A (normalize A) = true := extEq_normalize A
    have hb : extEq B (normalize B) = true := extEq_normalize B
    have hb_symm : extEq (normalize B) B = true := by rw [extEq_comm]; exact hb
    have h1 : extEq A (normalize B) = true := by rw [h] at ha; exact ha
    exact extEq_trans A (normalize B) B h1 hb_symm
