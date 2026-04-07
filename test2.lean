import AczelSetTheory.HFSets
import test

namespace HFSet

open CList

/-- Igualdad canónica entre HFSets: coinciden sus formas normales (repr). -/
def canonicalEq (A B : HFSet) : Prop :=
  A.repr = B.repr

theorem canonicalEq_iff_eq (A B : HFSet) : canonicalEq A B ↔ A = B := by
  constructor
  · intro h
    unfold canonicalEq at h
    rcases Quotient.exists_rep A with ⟨a, rfl⟩
    rcases Quotient.exists_rep B with ⟨b, rfl⟩
    apply Quotient.sound
    show extEq a b = true
    have h_norm : normalize a = normalize b := h
    exact extEq_iff_normalize_eq.mpr h_norm
  · intro h
    rw [h]
    unfold canonicalEq
    rfl

end HFSet
