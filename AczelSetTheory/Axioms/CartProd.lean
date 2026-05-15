/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/CartProd.lean
-- Teoremas de membresía para el producto cartesiano computable.

import AczelSetTheory.Operations.CartProd
import AczelSetTheory.Axioms.OrderedPair

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Membresía en cartProd
-- ─────────────────────────────────────────────────────────────────

/-- z ∈ A ×ₕ B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫ -/
theorem mem_cartProd (z A B : HFSet) :
    z ∈ A ×ₕ B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫ := by
  rcases Quotient.exists_rep z with ⟨zc, rfl⟩
  rcases Quotient.exists_rep A with ⟨ac, rfl⟩
  rcases Quotient.exists_rep B with ⟨bc, rfl⟩
  cases ac with | mk as =>
  cases bc with | mk bs =>
  change CList.mem zc (cartProdCList (CList.mk as) (CList.mk bs)) = true ↔ _
  rw [mem_cartProdCList_iff]
  constructor
  · rintro ⟨a, b, ha, hb, hz⟩
    exact ⟨Quotient.mk CList.Setoid a, Quotient.mk CList.Setoid b,
           ha, hb, by rw [orderedPair_eq_mk]; exact Quotient.sound hz⟩
  · rintro ⟨a_hf, b_hf, ha, hb, hz⟩
    rcases Quotient.exists_rep a_hf with ⟨a, rfl⟩
    rcases Quotient.exists_rep b_hf with ⟨b, rfl⟩
    exact ⟨a, b, ha, hb, by rw [orderedPair_eq_mk] at hz; exact Quotient.exact hz⟩

-- ─────────────────────────────────────────────────────────────────
-- Par ordenado pertenece al producto cartesiano
-- ─────────────────────────────────────────────────────────────────

/-- Si a ∈ A y b ∈ B, entonces ⟪a, b⟫ ∈ A ×ₕ B. -/
theorem mem_cartProd_pair (a b A B : HFSet) (ha : a ∈ A) (hb : b ∈ B) :
    ⟪a, b⟫ ∈ A ×ₕ B :=
  (mem_cartProd ⟪a, b⟫ A B).mpr ⟨a, b, ha, hb, rfl⟩

-- ─────────────────────────────────────────────────────────────────
-- Producto con el vacío
-- ─────────────────────────────────────────────────────────────────

/-- El producto cartesiano con el vacío a la izquierda es vacío. -/
theorem cartProd_empty_left (B : HFSet) : empty ×ₕ B = empty := by
  apply extensionality
  intro z
  constructor
  · intro h
    rw [mem_cartProd] at h
    obtain ⟨_, _, ha, _, _⟩ := h
    exact absurd ha (not_mem_empty _)
  · intro h
    exact absurd h (not_mem_empty _)

/-- El producto cartesiano con el vacío a la derecha es vacío. -/
theorem cartProd_empty_right (A : HFSet) : A ×ₕ empty = empty := by
  apply extensionality
  intro z
  constructor
  · intro h
    rw [mem_cartProd] at h
    obtain ⟨_, _, _, hb, _⟩ := h
    exact absurd hb (not_mem_empty _)
  · intro h
    exact absurd h (not_mem_empty _)

-- ─────────────────────────────────────────────────────────────────
-- cartProd es una relación
-- ─────────────────────────────────────────────────────────────────

/-- Todo elemento de A ×ₕ B es un par ordenado. -/
theorem cartProd_isRelation (A B : HFSet) :
    ∀ z, z ∈ A ×ₕ B → ∃ a b, z = ⟪a, b⟫ := by
  intro z hz
  rw [mem_cartProd] at hz
  obtain ⟨a, b, _, _, hz_eq⟩ := hz
  exact ⟨a, b, hz_eq⟩

end HFSet
