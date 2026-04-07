import AczelSetTheory.Operations.Pair
import AczelSetTheory.HFSets

namespace HFSet

/-- Axioma de Pares: x ∈ pair a b ↔ x = a ∨ x = b. -/
theorem mem_pair (x a b : HFSet) : x ∈ pair a b ↔ x = a ∨ x = b := by
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  rcases Quotient.exists_rep a with ⟨ac, rfl⟩
  rcases Quotient.exists_rep b with ⟨bc, rfl⟩
  change CList.mem xc (mkPair ac bc) = true ↔ _
  simp only [mkPair, CList.mem_cons, CList.mem_nil, Bool.or_false, Bool.or_eq_true]
  constructor
  · rintro (hxa | hxb)
    · exact Or.inl (Quotient.sound hxa)
    · exact Or.inr (Quotient.sound hxb)
  · rintro (hxa | hxb)
    · exact Or.inl (Quotient.exact hxa)
    · exact Or.inr (Quotient.exact hxb)

end HFSet
