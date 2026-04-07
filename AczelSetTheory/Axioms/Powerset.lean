import AczelSetTheory.Operations.Powerset
import AczelSetTheory.Axioms.Separation

namespace HFSet

-- subset for CList and HFSet is defined.
-- Actually we might need subset on HFSet if it's not there.
-- Let's just use `forall x, x \in B -> x \in A`

theorem mem_powerset (A : HFSet) (B : HFSet) :
    B ∈ powerset A ↔ (∀ x, x ∈ B → x ∈ A) := by
  sorry

end HFSet