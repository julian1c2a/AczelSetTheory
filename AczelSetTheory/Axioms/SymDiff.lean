import AczelSetTheory.Operations.SymDiff
import AczelSetTheory.Axioms.Setminus
import AczelSetTheory.Axioms.Union

namespace HFSet

theorem mem_symDiff
  (A B : HFSet) (x : HFSet) :
    x ∈ symDiff A B ↔ (x ∈ A ∧ ¬ x ∈ B) ∨ (x ∈ B ∧ ¬ x ∈ A)
      := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  rcases Quotient.exists_rep B with ⟨b, rfl⟩
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  change CList.mem xc (symDiffCList a b) = true ↔ _
  unfold symDiffCList
  rw [CList.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl ((mem_setminusCList_iff a b xc).mp h |>.imp id (Bool.eq_false_iff.mp ·))
    · exact Or.inr ((mem_setminusCList_iff b a xc).mp h |>.imp id (Bool.eq_false_iff.mp ·))
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact Or.inl ((mem_setminusCList_iff a b xc).mpr ⟨ha, Bool.eq_false_iff.mpr hb⟩)
    · exact Or.inr ((mem_setminusCList_iff b a xc).mpr ⟨hb, Bool.eq_false_iff.mpr ha⟩)

end HFSet
