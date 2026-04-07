import AczelSetTheory.Operations.Intersection
import AczelSetTheory.HFSets

namespace HFSet

theorem mem_interCList_iff
  (a b xc : CList) :
    CList.mem xc (interCList a b) = true ↔ CList.mem xc a = true ∧ CList.mem xc b = true
      := by
  cases a with
  | mk xs =>
  dsimp [interCList]
  have hP_resp : CList.P_respects (fun c => CList.mem c b)
    := by
    intro x y heq
    dsimp
    cases h1 : CList.mem x b
    · cases h2 : CList.mem y b
      · rfl
      · have := (mem_resp_left x y b heq).mpr h2
        rw [h1] at this; contradiction
    · cases h2 : CList.mem y b
      · have := (mem_resp_left x y b heq).mp h1
        rw [h2] at this; contradiction
      · rfl
  constructor
  · intro h
    have hPx : CList.mem xc b = true := CList.P_of_mem_filter (fun c => CList.mem c b) hP_resp xc xs h
    have h_mem : CList.mem xc (CList.mk xs) = true := CList.mem_subset xc (CList.mk (xs.filter (fun c => CList.mem c b))) (CList.mk xs) h (CList.subset_filter (fun c => CList.mem c b) xs)
    exact ⟨h_mem, hPx⟩
  · rintro ⟨h1, h2⟩
    exact CList.mem_filter_of_mem (fun c => CList.mem c b) hP_resp xc xs h1 h2

theorem mem_inter
  (A B : HFSet) (x : HFSet) :
    x ∈ inter A B ↔ x ∈ A ∧ x ∈ B
      := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  rcases Quotient.exists_rep B with ⟨b, rfl⟩
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  change CList.mem xc (interCList a b) = true ↔ CList.mem xc a = true ∧ CList.mem xc b = true
  exact mem_interCList_iff a b xc

end HFSet
