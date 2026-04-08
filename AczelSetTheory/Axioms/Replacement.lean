/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import AczelSetTheory.Operations.Replacement
import AczelSetTheory.Axioms.Function

namespace HFSet

-- ==================================================================
-- Especificación de image (Axioma de Reemplazo)
-- ==================================================================

/-- Pertenencia a la imagen: y ∈ image f A ↔ ∃ x ∈ A, ⟪x, y⟫ ∈ f. -/
theorem mem_image
  (f A y : HFSet) :
    y ∈ image f A ↔ ∃ x, x ∈ A ∧ ⟪x, y⟫ ∈ f
      := by
  unfold image
  rw [mem_sep]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨x, hxA, hxy⟩
    exact ⟨mem_range_of_mem f x y hxy, x, hxA, hxy⟩

/-- La imagen del vacío es vacía. -/
theorem image_empty
  (f : HFSet) :
    image f empty = empty
      := by
  apply extensionality
  intro x
  rw [mem_image]
  constructor
  · rintro ⟨a, ha, _⟩; exact absurd ha (not_mem_empty a)
  · intro h; exact absurd h (not_mem_empty x)

/-- La imagen bajo ∅ es ∅. -/
theorem image_of_empty
  (A : HFSet) :
    image empty A = empty
      := by
  apply extensionality
  intro x
  rw [mem_image]
  constructor
  · rintro ⟨_, _, h⟩; exact absurd h (not_mem_empty _)
  · intro h; exact absurd h (not_mem_empty x)

/-- La imagen está contenida en el rango. -/
theorem image_subset_range
  (f A y : HFSet) (h : y ∈ image f A) :
    y ∈ range f
      := by
  rw [mem_image] at h
  obtain ⟨x, _, hxy⟩ := h
  exact mem_range_of_mem f x y hxy

/-- Si f es función y x ∈ A ∩ domain f, entonces apply f x ∈ image f A. -/
theorem apply_mem_image
  (f A x : HFSet) (hf : isFunction f) (hxA : x ∈ A) (hx : ∃ b, ⟪x, b⟫ ∈ f) :
    apply f x hx ∈ image f A
      := by
  rw [mem_image]
  exact ⟨x, hxA, apply_mem f x hx⟩

/-- Si f es función total de A en B, la imagen de A es un subconjunto de B. -/
theorem image_totalFunction_subset
  (f A B y : HFSet) (hf : isTotalFunction f A B) (hy : y ∈ image f A) :
    y ∈ B
      := by
  rw [mem_image] at hy
  obtain ⟨x, _, hxy⟩ := hy
  exact hf.2.2 y (mem_range_of_mem f x y hxy)

end HFSet
