/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Canonical.lean
-- Representante canónico único para ℤ₀: `(0, n)` o `(n, 0)`.
--
-- ESTADO: M4B completo (cerrado 2026-06-05, commit b9484c7). 0 sorry.
--
-- DECISIÓN: ADR-014 — opción B: NO se introduce un tipo `HFInt` separado;
-- ℤ₀ = Quotient intSetoid se mantiene como único entero, pero se añade
-- `canonicalRep` para igualdad decidible eficiente.
--
-- API:
--   canonicalRep            : ℕ₀ × ℕ₀ → ℕ₀ × ℕ₀
--   canonicalRep_idempotent : ∀ p, canonicalRep (canonicalRep p) = canonicalRep p
--   canonicalRep_equiv      : ∀ p, intEq p (canonicalRep p)
--   canonicalRep_unique     : ∀ p q, intEq p q → canonicalRep p = canonicalRep q
--
-- `repr` y `mk_repr` viven en Basic.lean (via `normalize`); no se redefinen aquí.
--
-- Dependencies: AczelSetTheory.Integers.Basic
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Integers.Basic

open Peano Peano.Add Peano.Sub Peano.Order

namespace ℤ₀

-- ============================================================
-- Sección 1: Función canonicalRep
-- ============================================================

/-- Representante canónico: (p.1 - p.2, 0) si p.2 ≤ p.1, (0, p.2 - p.1) en caso contrario.
    Equivalente a `normalize` de Basic.lean pero como definición pública. -/
def canonicalRep (p : ℕ₀ × ℕ₀) : ℕ₀ × ℕ₀ :=
  if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)

theorem canonicalRep_equiv (p : ℕ₀ × ℕ₀) :
    intEq p (canonicalRep p) := by
  by_cases h : p.2 ≤ p.1
  · have hcr : canonicalRep p = (sub p.1 p.2, 𝟘) := by
      show (if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)) = (sub p.1 p.2, 𝟘)
      rw [if_pos h]
    rw [hcr]
    show add p.1 𝟘 = add p.2 (sub p.1 p.2)
    have h1 := sub_k_add_k p.1 p.2 h
    omega₀
  · have hcr : canonicalRep p = (𝟘, sub p.2 p.1) := by
      show (if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)) = (𝟘, sub p.2 p.1)
      rw [if_neg h]
    rw [hcr]
    show add p.1 (sub p.2 p.1) = add p.2 𝟘
    have hle : le₀ p.1 p.2 := lt_imp_le p.1 p.2 (nle_then_gt p.2 p.1 h)
    have h2 := sub_k_add_k p.2 p.1 hle
    omega₀

theorem canonicalRep_unique {p q : ℕ₀ × ℕ₀}
    (h : intEq p q) : canonicalRep p = canonicalRep q := by
  have h_eq : add p.1 q.2 = add p.2 q.1 := h
  by_cases hp : p.2 ≤ p.1 <;> by_cases hq : q.2 ≤ q.1
  · show (if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)) =
         if q.2 ≤ q.1 then (sub q.1 q.2, 𝟘) else (𝟘, sub q.2 q.1)
    rw [if_pos hp, if_pos hq]
    have h1 := sub_k_add_k p.1 p.2 hp
    have h2 := sub_k_add_k q.1 q.2 hq
    exact Prod.ext (by omega₀) rfl
  · exfalso
    have h1 := sub_k_add_k p.1 p.2 hp
    have hlt : lt₀ q.1 q.2 := nle_then_gt q.2 q.1 hq
    omega₀
  · exfalso
    have h2 := sub_k_add_k q.1 q.2 hq
    have hlt : lt₀ p.1 p.2 := nle_then_gt p.2 p.1 hp
    omega₀
  · show (if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)) =
         if q.2 ≤ q.1 then (sub q.1 q.2, 𝟘) else (𝟘, sub q.2 q.1)
    rw [if_neg hp, if_neg hq]
    have h1 := sub_k_add_k p.2 p.1 (lt_imp_le p.1 p.2 (nle_then_gt p.2 p.1 hp))
    have h2 := sub_k_add_k q.2 q.1 (lt_imp_le q.1 q.2 (nle_then_gt q.2 q.1 hq))
    exact Prod.ext rfl (by omega₀)

@[simp] theorem canonicalRep_idempotent (p : ℕ₀ × ℕ₀) :
    canonicalRep (canonicalRep p) = canonicalRep p := by
  by_cases h : p.2 ≤ p.1
  · have hcr : canonicalRep p = (sub p.1 p.2, 𝟘) := by
      show (if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)) = (sub p.1 p.2, 𝟘)
      rw [if_pos h]
    rw [hcr]
    have hle : 𝟘 ≤ sub p.1 p.2 := zero_le _
    show (if 𝟘 ≤ sub p.1 p.2 then (sub (sub p.1 p.2) 𝟘, 𝟘) else (𝟘, sub 𝟘 (sub p.1 p.2))) = (sub p.1 p.2, 𝟘)
    rw [if_pos hle, sub_zero]
  · have hlt : lt₀ p.1 p.2 := nle_then_gt p.2 p.1 h
    have hpos : lt₀ 𝟘 (sub p.2 p.1) := sub_pos_of_lt hlt
    have hnle : ¬ sub p.2 p.1 ≤ 𝟘 := gt_then_nle_wp hpos
    have hcr : canonicalRep p = (𝟘, sub p.2 p.1) := by
      show (if p.2 ≤ p.1 then (sub p.1 p.2, 𝟘) else (𝟘, sub p.2 p.1)) = (𝟘, sub p.2 p.1)
      rw [if_neg h]
    rw [hcr]
    show (if sub p.2 p.1 ≤ 𝟘 then (sub 𝟘 (sub p.2 p.1), 𝟘) else (𝟘, sub (sub p.2 p.1) 𝟘)) = (𝟘, sub p.2 p.1)
    rw [if_neg hnle, sub_zero]

-- ============================================================
-- Sección 2: Relación con repr de Basic.lean
-- ============================================================

-- `repr` (y `mk_repr`) ya están definidos en Basic.lean usando `normalize`.
-- canonicalRep es proporcional a normalize: ambos producen representantes
-- intEq-equivalentes al original (demostrado por canonicalRep_equiv).
-- La igualdad pointwise `canonicalRep p = normalize p` se puede probar
-- pero no se necesita para el objetivo principal de M4B.

end ℤ₀
