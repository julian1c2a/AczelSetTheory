/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Notation

namespace HFSet

/-- Axioma de Adjunción: x ∈ insert b A ↔ x = b ∨ x ∈ A. -/
theorem mem_insert (x b A : HFSet) : x ∈ insert b A ↔ x = b ∨ x ∈ A := by
  rcases Quotient.exists_rep x with ⟨xc, rfl⟩
  rcases Quotient.exists_rep b with ⟨bc, rfl⟩
  rcases Quotient.exists_rep A with ⟨ac, rfl⟩
  cases ac with | mk ys =>
  change CList.mem xc (insertCList bc (CList.mk ys)) = true ↔ _
  simp only [insertCList, CList.mem_cons, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl (Quotient.sound h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Quotient.exact h)
    · exact Or.inr h

/-- El elemento insertado pertenece al resultado. -/
theorem mem_insert_self (b A : HFSet) : b ∈ insert b A := by
  rcases Quotient.exists_rep b with ⟨bc, rfl⟩
  rcases Quotient.exists_rep A with ⟨ac, rfl⟩
  cases ac with | mk ys =>
  change CList.mem bc (insertCList bc (CList.mk ys)) = true
  simp only [insertCList, CList.mem_cons, CList.extEq_refl, Bool.true_or]

/-- El conjunto con un elemento insertado nunca es vacío. -/
theorem insert_ne_empty (b A : HFSet) : insert b A ≠ empty :=
  fun h => absurd (h ▸ mem_insert_self b A) (not_mem_empty b)

end HFSet
