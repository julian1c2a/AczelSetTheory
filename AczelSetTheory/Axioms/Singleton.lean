import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Notation

namespace HFSet

/-- Axioma del Singleton: x ∈ {a} ↔ x = a. -/
theorem mem_singleton (x a : HFSet) :
    x ∈ singleton a ↔ x = a := by
  unfold singleton
  rw [mem_pair]
  exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩

end HFSet
