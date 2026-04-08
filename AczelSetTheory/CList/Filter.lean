import AczelSetTheory.CList.ExtEq

namespace CList

-- P will respect ExtEq
def P_respects (P : CList → Bool) : Prop :=
  ∀ (x y : CList), extEq x y = true → P x = P y

theorem subset_filter
  (P : CList → Bool) (xs : List CList) :
    subset (mk (xs.filter P)) (mk xs) = true
      := by
  induction xs with
  | nil => simp only [List.filter_nil, subset_nil]
  | cons z zs ih =>
    simp only [List.filter_cons]
    split
    · simp only [subset_cons, Bool.and_eq_true]
      have hz : mem z (mk (z :: zs)) = true := by
        simp only [mem_cons, extEq_refl, Bool.true_or]
      have hsub : subset (mk (zs.filter P)) (mk (z :: zs)) = true := by
        exact subset_mono (zs.filter P) z zs ih
      exact ⟨hz, hsub⟩
    · exact subset_mono (zs.filter P) z zs ih

theorem mem_filter_of_mem
  (P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : List CList)
  (hx : mem x (mk xs) = true) (hPx : P x = true) :
    mem x (mk (xs.filter P)) = true
      := by
  induction xs with
  | nil => simp [mem_nil] at hx
  | cons z zs ih =>
    simp only [List.filter_cons]
    simp only [mem_cons, Bool.or_eq_true] at hx ⊢
    cases hx with
    | inl heq =>
      have hzP : P z = true := by
        have : P z = P x := hP_resp z x (extEq_comm x z ▸ heq)
        rw [this]
        exact hPx
      simp only [hzP, ite_true, mem_cons, Bool.or_eq_true]
      exact Or.inl heq
    | inr hmem =>
      have hind := ih hmem
      split
      · simp only [mem_cons, Bool.or_eq_true]
        exact Or.inr hind
      · exact hind

theorem filter_subset_filter
  (P : CList → Bool) (hP_resp : P_respects P) (xs ys : List CList)
  (hsub : subset (mk xs) (mk ys) = true) :
    subset (mk (xs.filter P)) (mk (ys.filter P)) = true
      := by
  induction xs with
  | nil => simp [List.filter_nil, subset_nil]
  | cons z zs ih =>
    simp only [List.filter_cons]
    split
    · next hzP =>
      simp only [subset_cons, Bool.and_eq_true]
      have hz_in_xs : mem z (mk (z :: zs)) = true := by simp only [mem_cons, extEq_refl, Bool.true_or]
      have hz_in_ys : mem z (mk ys) = true := mem_subset z (mk (z :: zs)) (mk ys) hz_in_xs hsub
      have hz_in_ys_filter : mem z (mk (ys.filter P)) = true := mem_filter_of_mem P hP_resp z ys hz_in_ys hzP
      have hzs_sub_ys : subset (mk zs) (mk ys) = true := by
        simp only [subset_cons, Bool.and_eq_true] at hsub
        exact hsub.2
      exact ⟨hz_in_ys_filter, ih hzs_sub_ys⟩
    · simp only [subset_cons, Bool.and_eq_true] at hsub
      exact ih hsub.2

theorem extEq_filter
  (P : CList → Bool) (hP_resp : P_respects P) (xs ys : List CList)
  (heq : extEq (mk xs) (mk ys) = true) :
    extEq (mk (xs.filter P)) (mk (ys.filter P)) = true
      := by
  simp only [extEq_def, Bool.and_eq_true] at heq ⊢
  exact ⟨filter_subset_filter P hP_resp xs ys heq.1, filter_subset_filter P hP_resp ys xs heq.2⟩


theorem P_of_mem_filter
  (P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : List CList)
  (hx : mem x (mk (xs.filter P)) = true) :
    P x = true
      := by
  induction xs with
  | nil => simp [mem_nil] at hx
  | cons z zs ih =>
    simp only [List.filter_cons] at hx
    split at hx
    · next hzP =>
      simp only [mem_cons, Bool.or_eq_true] at hx
      cases hx with
      | inl heq =>
        have h_px_pz : P x = P z := hP_resp x z heq
        rw [h_px_pz]
        exact hzP
      | inr hmem =>
        exact ih hmem
    · exact ih hx

end CList
