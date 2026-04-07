import AczelSetTheory.Operations.Powerset
import AczelSetTheory.Axioms.Separation

namespace HFSet

/-- Axioma de Conjunto Potencia (Powerset) abstracto. -/
theorem mem_powerset
  (A : HFSet) (B : HFSet) :
    B ∈ powerset A ↔ (∀ x, x ∈ B → x ∈ A)
      := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  rcases Quotient.exists_rep B with ⟨b, rfl⟩
  change CList.mem b (powersetCList a) = true ↔ _
  rw [mem_powersetCList]
  rw [subset_iff_forall_mem_clist]
  constructor
  · intro h x
    rcases Quotient.exists_rep x with ⟨xc, rfl⟩
    exact h xc
  · intro h xc
    exact h (Quotient.mk CList.Setoid xc)

end HFSet
