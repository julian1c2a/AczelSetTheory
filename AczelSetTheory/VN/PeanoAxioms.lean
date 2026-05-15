/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/PeanoAxioms.lean
-- Axiomas de Peano en HFSet y su transporte mediante vN.
--
-- Reformula PA1, PA2, PA3 como enunciados sobre HFSet.isNat
-- (delegando a Axioms/Succ.lean y Axioms/VonNeumann.lean),
-- y los transporta a la imagen de vN.
--
-- Contenido (nivel HFSet.isNat):
--   isNat_succ_ne_zero    : PA1 — el sucesor nunca es vacío
--   isNat_succ_injective  : PA2 — el sucesor es inyectivo
--   isNat_induction       : PA3 — inducción sobre isNat
--
-- Contenido (imagen de vN):
--   vN_zero_ne_succ       : vN 𝟘 ≠ vN (σ n)
--   vN_succ_injective_vN  : vN (σ m) = vN (σ n) → m = n
--   vN_induction          : inducción sobre la imagen de vN

import AczelSetTheory.VN.Injective
import AczelSetTheory.VN.IsNat

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Axiomas de Peano como enunciados puros sobre HFSet.isNat
-- ─────────────────────────────────────────────────────────────────

/-- PA1: El sucesor de un natural de von Neumann no es el conjunto vacío. -/
theorem isNat_succ_ne_zero (A : HFSet) (_ : HFSet.isNat A) :
    HFSet.succ A ≠ HFSet.empty :=
  HFSet.succ_ne_empty A

/-- PA2: El sucesor de von Neumann es inyectivo sobre los naturales. -/
theorem isNat_succ_injective (A B : HFSet) (_ : HFSet.isNat A) (_ : HFSet.isNat B)
    (h : HFSet.succ A = HFSet.succ B) : A = B :=
  HFSet.succ_injective A B h

/-- PA3: Principio de inducción para los naturales de von Neumann. -/
theorem isNat_induction (P : HFSet → Prop)
    (h0 : P HFSet.empty)
    (hs : ∀ k : HFSet, HFSet.isNat k → P k → P (HFSet.succ k))
    (n : HFSet) (hn : HFSet.isNat n) :
    P n :=
  HFSet.isNat_induction P h0 hs hn

-- ─────────────────────────────────────────────────────────────────
-- Transporte vía vN: los axiomas en la imagen de vN
-- ─────────────────────────────────────────────────────────────────

/-- vN-PA1: `vN 𝟘 ≠ vN (σ n)` para todo n : ℕ₀. -/
theorem vN_zero_ne_succ (n : ℕ₀) : vN 𝟘 ≠ vN (σ n) := by
  rw [vN_zero]
  exact fun h => vN_succ_ne_empty n h.symm

/-- vN-PA2: `vN (σ m) = vN (σ n) → m = n`. -/
theorem vN_succ_injective_vN (m n : ℕ₀) (h : vN (σ m) = vN (σ n)) : m = n := by
  simp only [vN_succ] at h
  exact vN_injective (HFSet.succ_injective _ _ h)

/-- vN-PA3: principio de inducción sobre la imagen de vN. -/
theorem vN_induction (P : HFSet → Prop)
    (h0 : P (vN 𝟘))
    (hs : ∀ n : ℕ₀, P (vN n) → P (vN (σ n)))
    (n : ℕ₀) : P (vN n) := by
  induction n with
  | zero => exact h0
  | succ k ih => exact hs k ih

end VN
