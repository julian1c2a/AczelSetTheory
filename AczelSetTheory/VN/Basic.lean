/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/Basic.lean
-- La función de Von Neumann vN : ℕ₀ → HFSet y sus propiedades básicas.
--
--   vN 𝟘     = ∅
--   vN (σ n) = HFSet.succ (vN n) = vN n ∪ {vN n}
--
-- Esto es la construcción clásica de los naturales de Von Neumann
-- dentro de HFSet, indexada por el tipo Peano ℕ₀.

import AczelSetTheory.Axioms

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición central
-- ─────────────────────────────────────────────────────────────────

/-- La función de Von Neumann: envía cada `n : ℕ₀` al conjunto finito
    hereditario `vN n`.

    - `vN 𝟘 = ∅`
    - `vN (σ n) = HFSet.succ (vN n) = vN n ∪ {vN n}` -/
def vN : ℕ₀ → HFSet
  | .zero   => HFSet.empty
  | .succ n => HFSet.succ (vN n)

-- ─────────────────────────────────────────────────────────────────
-- Ecuaciones definitionales
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem vN_zero : vN 𝟘 = HFSet.empty := rfl

@[simp] theorem vN_succ (n : ℕ₀) : vN (σ n) = HFSet.succ (vN n) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Propiedades inmediatas
-- ─────────────────────────────────────────────────────────────────

/-- El sucesor de Von Neumann nunca es vacío. -/
theorem vN_succ_ne_empty (n : ℕ₀) : vN (σ n) ≠ HFSet.empty := by
  simp only [vN_succ]
  exact HFSet.succ_ne_empty (vN n)

/-- Membresía en `vN (σ n)`: x pertenece al sucesor sii x ∈ vN n ó x = vN n. -/
theorem mem_vN_succ (x : HFSet) (n : ℕ₀) :
    x ∈ vN (σ n) ↔ x ∈ vN n ∨ x = vN n := by
  rw [vN_succ, HFSet.mem_succ]

/-- `vN n` pertenece a su propio sucesor. -/
theorem vN_mem_vN_succ (n : ℕ₀) : vN n ∈ vN (σ n) :=
  (mem_vN_succ (vN n) n).mpr (Or.inr rfl)

/-- `vN n` es subconjunto de `vN (σ n)`. -/
theorem vN_subset_vN_succ (n : ℕ₀) : vN n ⊆ vN (σ n) :=
  fun x hx => (mem_vN_succ x n).mpr (Or.inl hx)

end VN