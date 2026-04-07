import AczelSetTheory.Operations.Powerset
import AczelSetTheory.Axioms.Separation

namespace HFSet

/-- Axiona de Conjunto Potencia (Powerset) abstracto. -/
theorem mem_powerset
  (A : HFSet) (B : HFSet) :
    B ∈ powerset A ↔ (∀ x, x ∈ B → x ∈ A)
      := by
  sorry

end HFSet
