/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/NPow.lean
-- Teoremas de membresía para la n-ésima potencia cartesiana nPow A n.
--
-- Público:
--   mem_nPow_zero  : t ∈ nPow A 𝟘 ↔ t = empty
--   mem_nPow_succ  : t ∈ nPow A (σ n) ↔ ∃ s ∈ nPow A n, ∃ a ∈ A, t = ⟪s, a⟫
--
-- Semántica: nPow A n es el conjunto de "n-tuplas izquierdas" de elementos de A
-- codificadas como pares ordenados anidados:
--   nPow A 0 = {∅}
--   nPow A 1 = {∅} ×ₕ A  = {⟪∅, a⟫ | a ∈ A}
--   nPow A 2 = (nPow A 1) ×ₕ A = {⟪⟪∅,a₁⟫, a₂⟫ | a₁,a₂ ∈ A}

import AczelSetTheory.Operations.NPow
import AczelSetTheory.Axioms.CartProd
import AczelSetTheory.Axioms.Singleton

open Peano

namespace HFSet

-- ==================================================================
-- Membresía en nPow A 𝟘
-- ==================================================================

/-- El único elemento de nPow A 𝟘 = singleton empty es el conjunto vacío. -/
theorem mem_nPow_zero (t A : HFSet) : t ∈ nPow A 𝟘 ↔ t = empty := by
  rw [nPow_zero]
  exact mem_singleton t empty

-- ==================================================================
-- Membresía en nPow A (σ n)
-- ==================================================================

/-- t ∈ nPow A (σ n) ↔ t es un par ordenado ⟪s, a⟫ con s ∈ nPow A n y a ∈ A. -/
theorem mem_nPow_succ (t A : HFSet) (n : ℕ₀) :
    t ∈ nPow A (σ n) ↔ ∃ s ∈ nPow A n, ∃ a ∈ A, t = ⟪s, a⟫ := by
  rw [nPow_succ, mem_cartProd]
  constructor
  · rintro ⟨s, a, hs, ha, ht⟩
    exact ⟨s, hs, a, ha, ht⟩
  · rintro ⟨s, hs, a, ha, ht⟩
    exact ⟨s, a, hs, ha, ht⟩

end HFSet
