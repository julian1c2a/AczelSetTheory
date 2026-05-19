/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/ProdBridgeVN.lean
-- Bridge: ℕ₀ × ℕ₀ → HFSet vía par ordenado de Kuratowski.
--
-- prodBridge (m, n) := ⟪vN m, vN n⟫
--
-- Público:
--   prodBridge             : ℕ₀ × ℕ₀ → HFSet
--   prodBridge_mk          : prodBridge (m, n) = ⟪vN m, vN n⟫
--   prodBridge_injective   : Function.Injective prodBridge
--   prodBridge_isOrderedPair : ∃ a b, prodBridge p = ⟪a, b⟫
--   prodBridge_eq_iff      : prodBridge p = prodBridge q ↔ p = q

import AczelSetTheory.VN.Injective
import AczelSetTheory.Axioms.OrderedPair

open Peano VN

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Embebe un par de naturales de Peano como par ordenado de Kuratowski
    en HFSet. -/
def prodBridge (p : ℕ₀ × ℕ₀) : HFSet := ⟪vN p.1, vN p.2⟫

-- ─────────────────────────────────────────────────────────────────
-- Propiedades
-- ─────────────────────────────────────────────────────────────────

@[simp]
theorem prodBridge_mk (m n : ℕ₀) : prodBridge (m, n) = ⟪vN m, vN n⟫ := rfl

theorem prodBridge_isOrderedPair (p : ℕ₀ × ℕ₀) :
    ∃ a b, prodBridge p = ⟪a, b⟫ :=
  ⟨vN p.1, vN p.2, rfl⟩

theorem prodBridge_injective : Function.Injective prodBridge := by
  intro ⟨m₁, n₁⟩ ⟨m₂, n₂⟩ h
  simp only [prodBridge, orderedPair_eq_iff] at h
  exact Prod.ext (vN_injective h.1) (vN_injective h.2)

theorem prodBridge_eq_iff (p q : ℕ₀ × ℕ₀) :
    prodBridge p = prodBridge q ↔ p = q :=
  prodBridge_injective.eq_iff

theorem prodBridge_components (m n : ℕ₀) {a b : HFSet}
    (h : prodBridge (m, n) = ⟪a, b⟫) : a = vN m ∧ b = vN n := by
  rw [prodBridge_mk, orderedPair_eq_iff] at h
  exact ⟨h.1.symm, h.2.symm⟩

end HFSet
