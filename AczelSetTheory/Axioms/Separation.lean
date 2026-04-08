import AczelSetTheory.HFSets
import AczelSetTheory.Operations.Separation

namespace HFSet

theorem mem_filterCList_iff
  (a xc : CList) (P : HFSet -> Prop) [DecidablePred P] :
    CList.mem xc (filterCList P a) = true ↔ CList.mem xc a = true ∧ P (Quotient.mk CList.Setoid xc)
      := by
  cases a with
  | mk xs =>
  dsimp [filterCList]
  have hP_resp : CList.P_respects (fun c => decide (P (Quotient.mk CList.Setoid c))) := by
    intro x y heq
    have hQuot : Quotient.mk CList.Setoid x = Quotient.mk CList.Setoid y := Quotient.sound heq
    simp only [hQuot]
  constructor
  · intro h
    have hPx : decide (P (Quotient.mk CList.Setoid xc)) = true := CList.P_of_mem_filter (fun c => decide (P (Quotient.mk CList.Setoid c))) hP_resp xc xs h
    have h_mem : CList.mem xc (CList.mk xs) = true := CList.mem_subset xc (CList.mk (xs.filter (fun c => decide (P (Quotient.mk CList.Setoid c))))) (CList.mk xs) h (CList.subset_filter (fun c => decide (P (Quotient.mk CList.Setoid c))) xs)
    exact ⟨h_mem, of_decide_eq_true hPx⟩
  · rintro ⟨h1, h2⟩
    have hzP : decide (P (Quotient.mk CList.Setoid xc)) = true := decide_eq_true h2
    exact CList.mem_filter_of_mem (fun c => decide (P (Quotient.mk CList.Setoid c))) hP_resp xc xs h1 hzP

theorem mem_sep
  (A : HFSet) (P : HFSet -> Prop) [DecidablePred P] (x : HFSet) :
    x ∈ sep A P ↔ x ∈ A ∧ P x
      := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  change CList.mem xc (filterCList P a) = true ↔ CList.mem xc a = true ∧ P (Quotient.mk CList.Setoid xc)
  exact mem_filterCList_iff a xc P

end HFSet
