import AczelSetTheory.HFSets
import AczelSetTheory.Operations.Union

namespace HFSet

theorem mem_union (z A B : HFSet) : z ∈ union A B ↔ z ∈ A ∨ z ∈ B := by
  rcases Quotient.exists_rep z with ⟨zc, rfl⟩
  rcases Quotient.exists_rep A with ⟨Ac, rfl⟩
  rcases Quotient.exists_rep B with ⟨Bc, rfl⟩
  change CList.mem zc (CList.union Ac Bc) = true ↔ CList.mem zc Ac = true ∨ CList.mem zc Bc = true
  exact CList.mem_union zc Ac Bc

theorem mem_sUnion (z A : HFSet) : z ∈ sUnion A ↔ ∃ Y : HFSet, Y ∈ A ∧ z ∈ Y := by
  rcases Quotient.exists_rep z with ⟨zc, rfl⟩
  rcases Quotient.exists_rep A with ⟨Ac, rfl⟩
  constructor
  · intro h
    have h1 : CList.mem zc (CList.sUnion Ac) = true := h
    rw [CList.mem_sUnion] at h1
    rcases h1 with ⟨Yc, hYc_in_A, hz_in_Yc⟩
    exact ⟨Quotient.mk CList.Setoid Yc, hYc_in_A, hz_in_Yc⟩
  · rintro ⟨Y, hY_in_A, hz_in_Y⟩
    rcases Quotient.exists_rep Y with ⟨Yc, rfl⟩
    have hz_in_Yc' : CList.mem zc Yc = true := hz_in_Y
    have hYc_in_Ac' : CList.mem Yc Ac = true := hY_in_A
    have h1 : CList.mem zc (CList.sUnion Ac) = true := by
      rw [CList.mem_sUnion]
      exact ⟨Yc, hYc_in_Ac', hz_in_Yc'⟩
    exact h1

end HFSet
