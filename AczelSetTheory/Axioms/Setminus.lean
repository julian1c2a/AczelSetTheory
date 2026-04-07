import AczelSetTheory.Operations.Setminus
import AczelSetTheory.HFSets

namespace HFSet

theorem mem_setminusCList_iff (a b xc : CList) :
    CList.mem xc (setminusCList a b) = true ↔ CList.mem xc a = true ∧ CList.mem xc b = false := by
  cases a with | mk xs =>
  dsimp [setminusCList]
  have hP_resp : CList.P_respects (fun c => !(CList.mem c b)) := by
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
    have hPx : (!(CList.mem xc b)) = true := CList.P_of_mem_filter (fun c => !(CList.mem c b)) hP_resp xc xs h
    have h_mem : CList.mem xc (CList.mk xs) = true := CList.mem_subset xc (CList.mk (xs.filter (fun c => !(CList.mem c b)))) (CList.mk xs) h (CList.subset_filter (fun c => !(CList.mem c b)) xs)
    have hxcb_false : CList.mem xc b = false := by cases hc : CList.mem xc b; rfl; rw [hc] at hPx; contradiction
    exact ⟨h_mem, hxcb_false⟩
  · rintro ⟨h1, h2⟩
    have hPx_true : (!(CList.mem xc b)) = true := by rw [h2]; rfl
    exact CList.mem_filter_of_mem (fun c => !(CList.mem c b)) hP_resp xc xs h1 hPx_true

theorem mem_setminus (A B : HFSet) (x : HFSet) :  
    x ∈ setminus A B ↔ x ∈ A ∧ ¬ (x ∈ B) := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  rcases Quotient.exists_rep B with ⟨b, rfl⟩
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  change CList.mem xc (setminusCList a b) = true ↔ CList.mem xc a = true ∧ ¬ (CList.mem xc b = true)
  have h_iff := mem_setminusCList_iff a b xc
  have h_not : CList.mem xc b = false ↔ ¬ (CList.mem xc b = true) := by
    constructor
    · intro h1 h2; rw [h1] at h2; contradiction
    · intro hnot; cases hc : CList.mem xc b
      · rfl
      · specialize hnot hc; contradiction
  rw [h_not] at h_iff
  exact h_iff

end HFSet
